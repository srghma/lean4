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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_Rcc_toList___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Std_Rcc_toList___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Rcc_toList___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Std_Rcc_Internal_iter___redArg(mut v_r_1272_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lower_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1277_: u8 = 0;
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1273_ = lean_ctor_get(v_r_1272_, 0);
                v_upper_1274_ = lean_ctor_get(v_r_1272_, 1);
                v_isSharedCheck_1282_ = (!lean_is_exclusive(v_r_1272_)) as u8;
                if v_isSharedCheck_1282_ == 0 {
                    v___x_1276_ = v_r_1272_;
                    v_isShared_1277_ = v_isSharedCheck_1282_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1274_);
                    lean_inc(v_lower_1273_);
                    lean_dec(v_r_1272_);
                    v___x_1276_ = lean_box(0);
                    v_isShared_1277_ = v_isSharedCheck_1282_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1278_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1278_, 0, v_lower_1273_);
                if v_isShared_1277_ == 0 {
                    lean_ctor_set(v___x_1276_, 0, v___x_1278_);
                    v___x_1280_ = v___x_1276_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
                    lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_upper_1274_);
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
    mut v_00_u03b1_1283_: *mut LeanObject,
    mut v_inst_1284_: *mut LeanObject,
    mut v_r_1285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1290_: u8 = 0;
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1286_ = lean_ctor_get(v_r_1285_, 0);
                v_upper_1287_ = lean_ctor_get(v_r_1285_, 1);
                v_isSharedCheck_1295_ = (!lean_is_exclusive(v_r_1285_)) as u8;
                if v_isSharedCheck_1295_ == 0 {
                    v___x_1289_ = v_r_1285_;
                    v_isShared_1290_ = v_isSharedCheck_1295_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1287_);
                    lean_inc(v_lower_1286_);
                    lean_dec(v_r_1285_);
                    v___x_1289_ = lean_box(0);
                    v_isShared_1290_ = v_isSharedCheck_1295_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1291_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1291_, 0, v_lower_1286_);
                if v_isShared_1290_ == 0 {
                    lean_ctor_set(v___x_1289_, 0, v___x_1291_);
                    v___x_1293_ = v___x_1289_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
                    lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_upper_1287_);
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
    mut v_00_u03b1_1296_: *mut LeanObject,
    mut v_inst_1297_: *mut LeanObject,
    mut v_r_1298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1299_: *mut LeanObject = core::ptr::null_mut();
    v_res_1299_ = l_Std_Rcc_Internal_iter(v_00_u03b1_1296_, v_inst_1297_, v_r_1298_);
    lean_dec_ref(v_inst_1297_);
    return v_res_1299_;
}
pub unsafe fn l_Std_Rcc_toList___redArg___lam__0(
    mut v_inst_1300_: *mut LeanObject,
    mut v_inst_1301_: *mut LeanObject,
    mut v_it_1302_: *mut LeanObject,
    mut v_acc_1303_: *mut LeanObject,
    mut v_recur_1304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1309_: u8 = 0;
    let mut v_val_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: u8 = 0;
    let mut v_succ_x3f_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1320_: u8 = 0;
    let mut v_unused_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1305_ = lean_ctor_get(v_it_1302_, 0);
                lean_inc(v_next_1305_);
                if lean_obj_tag(v_next_1305_) == 0 {
                    lean_dec_ref(v_recur_1304_);
                    lean_dec_ref(v_it_1302_);
                    lean_dec_ref(v_inst_1301_);
                    lean_dec_ref(v_inst_1300_);
                    return v_acc_1303_;
                } else {
                    v_upperBound_1306_ = lean_ctor_get(v_it_1302_, 1);
                    v_isSharedCheck_1320_ = (!lean_is_exclusive(v_it_1302_)) as u8;
                    if v_isSharedCheck_1320_ == 0 {
                        v_unused_1321_ = lean_ctor_get(v_it_1302_, 0);
                        lean_dec(v_unused_1321_);
                        v___x_1308_ = v_it_1302_;
                        v_isShared_1309_ = v_isSharedCheck_1320_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_upperBound_1306_);
                        lean_dec(v_it_1302_);
                        v___x_1308_ = lean_box(0);
                        v_isShared_1309_ = v_isSharedCheck_1320_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1310_ = lean_ctor_get(v_next_1305_, 0);
                lean_inc_n(v_val_1310_, 2);
                lean_dec_ref_known(v_next_1305_, 1);
                lean_inc(v_upperBound_1306_);
                v___x_1311_ = lean_apply_2(v_inst_1300_, v_val_1310_, v_upperBound_1306_);
                v___x_1312_ = (lean_unbox(v___x_1311_) as u8);
                if v___x_1312_ == 0 {
                    lean_dec(v_val_1310_);
                    lean_del_object(v___x_1308_);
                    lean_dec(v_upperBound_1306_);
                    lean_dec_ref(v_recur_1304_);
                    lean_dec_ref(v_inst_1301_);
                    return v_acc_1303_;
                } else {
                    v_succ_x3f_1313_ = lean_ctor_get(v_inst_1301_, 0);
                    lean_inc_ref(v_succ_x3f_1313_);
                    lean_dec_ref(v_inst_1301_);
                    lean_inc(v_val_1310_);
                    v___x_1314_ = lean_apply_1(v_succ_x3f_1313_, v_val_1310_);
                    if v_isShared_1309_ == 0 {
                        lean_ctor_set(v___x_1308_, 0, v___x_1314_);
                        v___x_1316_ = v___x_1308_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1314_);
                        lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_upperBound_1306_);
                        v___x_1316_ = v_reuseFailAlloc_1319_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1317_ = lean_array_push(v_acc_1303_, v_val_1310_);
                v___x_1318_ = lean_apply_3(v_recur_1304_, v___x_1316_, v___x_1317_, lean_box(0));
                return v___x_1318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rcc_toList___redArg(
    mut v_inst_1324_: *mut LeanObject,
    mut v_inst_1325_: *mut LeanObject,
    mut v_r_1326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1331_: u8 = 0;
    let mut v___f_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1340_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1327_ = lean_ctor_get(v_r_1326_, 0);
                v_upper_1328_ = lean_ctor_get(v_r_1326_, 1);
                v_isSharedCheck_1340_ = (!lean_is_exclusive(v_r_1326_)) as u8;
                if v_isSharedCheck_1340_ == 0 {
                    v___x_1330_ = v_r_1326_;
                    v_isShared_1331_ = v_isSharedCheck_1340_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1328_);
                    lean_inc(v_lower_1327_);
                    lean_dec(v_r_1326_);
                    v___x_1330_ = lean_box(0);
                    v_isShared_1331_ = v_isSharedCheck_1340_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1332_ = lean_alloc_closure(
                    l_Std_Rcc_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_1332_, 0, v_inst_1324_);
                lean_closure_set(v___f_1332_, 1, v_inst_1325_);
                v___x_1333_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1333_, 0, v_lower_1327_);
                if v_isShared_1331_ == 0 {
                    lean_ctor_set(v___x_1330_, 0, v___x_1333_);
                    v___x_1335_ = v___x_1330_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1333_);
                    lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_upper_1328_);
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
    mut v_00_u03b1_1341_: *mut LeanObject,
    mut v_inst_1342_: *mut LeanObject,
    mut v_inst_1343_: *mut LeanObject,
    mut v_inst_1344_: *mut LeanObject,
    mut v_inst_1345_: *mut LeanObject,
    mut v_inst_1346_: *mut LeanObject,
    mut v_r_1347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1352_: u8 = 0;
    let mut v___f_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1348_ = lean_ctor_get(v_r_1347_, 0);
                v_upper_1349_ = lean_ctor_get(v_r_1347_, 1);
                v_isSharedCheck_1361_ = (!lean_is_exclusive(v_r_1347_)) as u8;
                if v_isSharedCheck_1361_ == 0 {
                    v___x_1351_ = v_r_1347_;
                    v_isShared_1352_ = v_isSharedCheck_1361_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1349_);
                    lean_inc(v_lower_1348_);
                    lean_dec(v_r_1347_);
                    v___x_1351_ = lean_box(0);
                    v_isShared_1352_ = v_isSharedCheck_1361_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1353_ = lean_alloc_closure(
                    l_Std_Rcc_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_1353_, 0, v_inst_1343_);
                lean_closure_set(v___f_1353_, 1, v_inst_1344_);
                v___x_1354_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1354_, 0, v_lower_1348_);
                if v_isShared_1352_ == 0 {
                    lean_ctor_set(v___x_1351_, 0, v___x_1354_);
                    v___x_1356_ = v___x_1351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1354_);
                    lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_upper_1349_);
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
    mut v_inst_1362_: *mut LeanObject,
    mut v_inst_1363_: *mut LeanObject,
    mut v_r_1364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___f_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1365_ = lean_ctor_get(v_r_1364_, 0);
                v_upper_1366_ = lean_ctor_get(v_r_1364_, 1);
                v_isSharedCheck_1377_ = (!lean_is_exclusive(v_r_1364_)) as u8;
                if v_isSharedCheck_1377_ == 0 {
                    v___x_1368_ = v_r_1364_;
                    v_isShared_1369_ = v_isSharedCheck_1377_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1366_);
                    lean_inc(v_lower_1365_);
                    lean_dec(v_r_1364_);
                    v___x_1368_ = lean_box(0);
                    v_isShared_1369_ = v_isSharedCheck_1377_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1370_ = lean_alloc_closure(
                    l_Std_Rcc_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_1370_, 0, v_inst_1362_);
                lean_closure_set(v___f_1370_, 1, v_inst_1363_);
                v___x_1371_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1371_, 0, v_lower_1365_);
                if v_isShared_1369_ == 0 {
                    lean_ctor_set(v___x_1368_, 0, v___x_1371_);
                    v___x_1373_ = v___x_1368_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1371_);
                    lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_upper_1366_);
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
    mut v_00_u03b1_1378_: *mut LeanObject,
    mut v_inst_1379_: *mut LeanObject,
    mut v_inst_1380_: *mut LeanObject,
    mut v_inst_1381_: *mut LeanObject,
    mut v_inst_1382_: *mut LeanObject,
    mut v_inst_1383_: *mut LeanObject,
    mut v_r_1384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1389_: u8 = 0;
    let mut v___f_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1385_ = lean_ctor_get(v_r_1384_, 0);
                v_upper_1386_ = lean_ctor_get(v_r_1384_, 1);
                v_isSharedCheck_1397_ = (!lean_is_exclusive(v_r_1384_)) as u8;
                if v_isSharedCheck_1397_ == 0 {
                    v___x_1388_ = v_r_1384_;
                    v_isShared_1389_ = v_isSharedCheck_1397_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1386_);
                    lean_inc(v_lower_1385_);
                    lean_dec(v_r_1384_);
                    v___x_1388_ = lean_box(0);
                    v_isShared_1389_ = v_isSharedCheck_1397_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1390_ = lean_alloc_closure(
                    l_Std_Rcc_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_1390_, 0, v_inst_1380_);
                lean_closure_set(v___f_1390_, 1, v_inst_1381_);
                v___x_1391_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1391_, 0, v_lower_1385_);
                if v_isShared_1389_ == 0 {
                    lean_ctor_set(v___x_1388_, 0, v___x_1391_);
                    v___x_1393_ = v___x_1388_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1391_);
                    lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_upper_1386_);
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
    mut v_inst_1398_: *mut LeanObject,
    mut v_r_1399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    v_lower_1400_ = lean_ctor_get(v_r_1399_, 0);
    lean_inc(v_lower_1400_);
    v_upper_1401_ = lean_ctor_get(v_r_1399_, 1);
    lean_inc(v_upper_1401_);
    lean_dec_ref(v_r_1399_);
    v___x_1402_ = lean_apply_2(v_inst_1398_, v_lower_1400_, v_upper_1401_);
    return v___x_1402_;
}
pub unsafe fn l_Std_Rcc_size(
    mut v_00_u03b1_1403_: *mut LeanObject,
    mut v_inst_1404_: *mut LeanObject,
    mut v_r_1405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    v_lower_1406_ = lean_ctor_get(v_r_1405_, 0);
    lean_inc(v_lower_1406_);
    v_upper_1407_ = lean_ctor_get(v_r_1405_, 1);
    lean_inc(v_upper_1407_);
    lean_dec_ref(v_r_1405_);
    v___x_1408_ = lean_apply_2(v_inst_1404_, v_lower_1406_, v_upper_1407_);
    return v___x_1408_;
}
pub unsafe fn l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0(
    mut v_toPure_1409_: *mut LeanObject,
    mut v_____do__lift_1410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    v___x_1411_ = lean_apply_2(v_toPure_1409_, lean_box(0), v_____do__lift_1410_);
    return v___x_1411_;
}
pub unsafe fn l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__1(
    mut v_toPure_1412_: *mut LeanObject,
    mut v_inst_1413_: *mut LeanObject,
    mut v_next_1414_: *mut LeanObject,
    mut v_G_1415_: *mut LeanObject,
    mut v_____do__lift_1416_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1416_) == 0 {
        let mut v_a_1417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_G_1415_);
        lean_dec(v_next_1414_);
        lean_dec_ref(v_inst_1413_);
        v_a_1417_ = lean_ctor_get(v_____do__lift_1416_, 0);
        lean_inc(v_a_1417_);
        lean_dec_ref_known(v_____do__lift_1416_, 1);
        v___x_1418_ = lean_apply_2(v_toPure_1412_, lean_box(0), v_a_1417_);
        return v___x_1418_;
    } else {
        let mut v_a_1419_: *mut LeanObject = core::ptr::null_mut();
        let mut v_succ_x3f_1420_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
        v_a_1419_ = lean_ctor_get(v_____do__lift_1416_, 0);
        lean_inc(v_a_1419_);
        lean_dec_ref_known(v_____do__lift_1416_, 1);
        v_succ_x3f_1420_ = lean_ctor_get(v_inst_1413_, 0);
        lean_inc_ref(v_succ_x3f_1420_);
        lean_dec_ref(v_inst_1413_);
        v___x_1421_ = lean_apply_1(v_succ_x3f_1420_, v_next_1414_);
        if lean_obj_tag(v___x_1421_) == 0 {
            let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_G_1415_);
            v___x_1422_ = lean_apply_2(v_toPure_1412_, lean_box(0), v_a_1419_);
            return v___x_1422_;
        } else {
            let mut v_val_1423_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toPure_1412_);
            v_val_1423_ = lean_ctor_get(v___x_1421_, 0);
            lean_inc(v_val_1423_);
            lean_dec_ref_known(v___x_1421_, 1);
            v___x_1424_ = lean_apply_4(v_G_1415_, v_val_1423_, v_a_1419_, lean_box(0), lean_box(0));
            return v___x_1424_;
        }
    }
}
pub unsafe fn l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2(
    mut v_inst_1425_: *mut LeanObject,
    mut v_upper_1426_: *mut LeanObject,
    mut v_toPure_1427_: *mut LeanObject,
    mut v_inst_1428_: *mut LeanObject,
    mut v_f_1429_: *mut LeanObject,
    mut v_toBind_1430_: *mut LeanObject,
    mut v___f_1431_: *mut LeanObject,
    mut v_next_1432_: *mut LeanObject,
    mut v_acc_1433_: *mut LeanObject,
    mut v_h_1434_: *mut LeanObject,
    mut v_G_1435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: u8 = 0;
    lean_inc(v_next_1432_);
    v___x_1436_ = lean_apply_2(v_inst_1425_, v_next_1432_, v_upper_1426_);
    v___x_1437_ = (lean_unbox(v___x_1436_) as u8);
    if v___x_1437_ == 0 {
        let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_G_1435_);
        lean_dec(v_next_1432_);
        lean_dec(v___f_1431_);
        lean_dec(v_toBind_1430_);
        lean_dec(v_f_1429_);
        lean_dec_ref(v_inst_1428_);
        v___x_1438_ = lean_apply_2(v_toPure_1427_, lean_box(0), v_acc_1433_);
        return v___x_1438_;
    } else {
        let mut v___f_1439_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_next_1432_);
        v___f_1439_ = lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__1 as *mut core::ffi::c_void, 5, 4);
        lean_closure_set(v___f_1439_, 0, v_toPure_1427_);
        lean_closure_set(v___f_1439_, 1, v_inst_1428_);
        lean_closure_set(v___f_1439_, 2, v_next_1432_);
        lean_closure_set(v___f_1439_, 3, v_G_1435_);
        v___x_1440_ = lean_apply_3(v_f_1429_, v_next_1432_, lean_box(0), v_acc_1433_);
        lean_inc(v_toBind_1430_);
        v___x_1441_ = lean_apply_4(
            v_toBind_1430_,
            lean_box(0),
            lean_box(0),
            v___x_1440_,
            v___f_1431_,
        );
        v___x_1442_ = lean_apply_4(
            v_toBind_1430_,
            lean_box(0),
            lean_box(0),
            v___x_1441_,
            v___f_1439_,
        );
        return v___x_1442_;
    }
}
pub unsafe fn l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__3(
    mut v_inst_1443_: *mut LeanObject,
    mut v_inst_1444_: *mut LeanObject,
    mut v_inst_1445_: *mut LeanObject,
    mut v_00_u03b2_1446_: *mut LeanObject,
    mut v_r_1447_: *mut LeanObject,
    mut v_init_1448_: *mut LeanObject,
    mut v_f_1449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1450_ = lean_ctor_get(v_inst_1443_, 0);
    lean_inc_ref(v_toApplicative_1450_);
    v_lower_1451_ = lean_ctor_get(v_r_1447_, 0);
    lean_inc(v_lower_1451_);
    v_upper_1452_ = lean_ctor_get(v_r_1447_, 1);
    lean_inc(v_upper_1452_);
    lean_dec_ref(v_r_1447_);
    v_toBind_1453_ = lean_ctor_get(v_inst_1443_, 1);
    lean_inc(v_toBind_1453_);
    lean_dec_ref(v_inst_1443_);
    v_toPure_1454_ = lean_ctor_get(v_toApplicative_1450_, 1);
    lean_inc_n(v_toPure_1454_, 2);
    lean_dec_ref(v_toApplicative_1450_);
    v___f_1455_ = lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_1455_, 0, v_toPure_1454_);
    v___f_1456_ = lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2 as *mut core::ffi::c_void, 11, 7);
    lean_closure_set(v___f_1456_, 0, v_inst_1444_);
    lean_closure_set(v___f_1456_, 1, v_upper_1452_);
    lean_closure_set(v___f_1456_, 2, v_toPure_1454_);
    lean_closure_set(v___f_1456_, 3, v_inst_1445_);
    lean_closure_set(v___f_1456_, 4, v_f_1449_);
    lean_closure_set(v___f_1456_, 5, v_toBind_1453_);
    lean_closure_set(v___f_1456_, 6, v___f_1455_);
    v___x_1457_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1456_,
        v_lower_1451_,
        v_init_1448_,
        lean_box(0),
    );
    return v___x_1457_;
}
pub unsafe fn l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_1458_: *mut LeanObject,
    mut v_inst_1459_: *mut LeanObject,
    mut v_inst_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1461_: *mut LeanObject = core::ptr::null_mut();
    v___f_1461_ = lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__3 as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___f_1461_, 0, v_inst_1460_);
    lean_closure_set(v___f_1461_, 1, v_inst_1459_);
    lean_closure_set(v___f_1461_, 2, v_inst_1458_);
    return v___f_1461_;
}
pub unsafe fn l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_1462_: *mut LeanObject,
    mut v_m_1463_: *mut LeanObject,
    mut v_inst_1464_: *mut LeanObject,
    mut v_inst_1465_: *mut LeanObject,
    mut v_inst_1466_: *mut LeanObject,
    mut v_inst_1467_: *mut LeanObject,
    mut v_inst_1468_: *mut LeanObject,
    mut v_inst_1469_: *mut LeanObject,
    mut v_inst_1470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1471_: *mut LeanObject = core::ptr::null_mut();
    v___f_1471_ = lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__3 as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___f_1471_, 0, v_inst_1469_);
    lean_closure_set(v___f_1471_, 1, v_inst_1466_);
    lean_closure_set(v___f_1471_, 2, v_inst_1464_);
    return v___f_1471_;
}
pub unsafe fn l_Std_Rco_Internal_iter___redArg(mut v_r_1472_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lower_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1477_: u8 = 0;
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1473_ = lean_ctor_get(v_r_1472_, 0);
                v_upper_1474_ = lean_ctor_get(v_r_1472_, 1);
                v_isSharedCheck_1482_ = (!lean_is_exclusive(v_r_1472_)) as u8;
                if v_isSharedCheck_1482_ == 0 {
                    v___x_1476_ = v_r_1472_;
                    v_isShared_1477_ = v_isSharedCheck_1482_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1474_);
                    lean_inc(v_lower_1473_);
                    lean_dec(v_r_1472_);
                    v___x_1476_ = lean_box(0);
                    v_isShared_1477_ = v_isSharedCheck_1482_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1478_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1478_, 0, v_lower_1473_);
                if v_isShared_1477_ == 0 {
                    lean_ctor_set(v___x_1476_, 0, v___x_1478_);
                    v___x_1480_ = v___x_1476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
                    lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_upper_1474_);
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
    mut v_00_u03b1_1483_: *mut LeanObject,
    mut v_inst_1484_: *mut LeanObject,
    mut v_r_1485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1490_: u8 = 0;
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1495_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1486_ = lean_ctor_get(v_r_1485_, 0);
                v_upper_1487_ = lean_ctor_get(v_r_1485_, 1);
                v_isSharedCheck_1495_ = (!lean_is_exclusive(v_r_1485_)) as u8;
                if v_isSharedCheck_1495_ == 0 {
                    v___x_1489_ = v_r_1485_;
                    v_isShared_1490_ = v_isSharedCheck_1495_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1487_);
                    lean_inc(v_lower_1486_);
                    lean_dec(v_r_1485_);
                    v___x_1489_ = lean_box(0);
                    v_isShared_1490_ = v_isSharedCheck_1495_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1491_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1491_, 0, v_lower_1486_);
                if v_isShared_1490_ == 0 {
                    lean_ctor_set(v___x_1489_, 0, v___x_1491_);
                    v___x_1493_ = v___x_1489_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
                    lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_upper_1487_);
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
    mut v_00_u03b1_1496_: *mut LeanObject,
    mut v_inst_1497_: *mut LeanObject,
    mut v_r_1498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1499_: *mut LeanObject = core::ptr::null_mut();
    v_res_1499_ = l_Std_Rco_Internal_iter(v_00_u03b1_1496_, v_inst_1497_, v_r_1498_);
    lean_dec_ref(v_inst_1497_);
    return v_res_1499_;
}
pub unsafe fn l_Std_Rco_toList___redArg___lam__0(
    mut v_inst_1500_: *mut LeanObject,
    mut v_inst_1501_: *mut LeanObject,
    mut v_it_1502_: *mut LeanObject,
    mut v_acc_1503_: *mut LeanObject,
    mut v_recur_1504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1509_: u8 = 0;
    let mut v_val_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: u8 = 0;
    let mut v_succ_x3f_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1520_: u8 = 0;
    let mut v_unused_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1505_ = lean_ctor_get(v_it_1502_, 0);
                lean_inc(v_next_1505_);
                if lean_obj_tag(v_next_1505_) == 0 {
                    lean_dec_ref(v_recur_1504_);
                    lean_dec_ref(v_it_1502_);
                    lean_dec_ref(v_inst_1501_);
                    lean_dec_ref(v_inst_1500_);
                    return v_acc_1503_;
                } else {
                    v_upperBound_1506_ = lean_ctor_get(v_it_1502_, 1);
                    v_isSharedCheck_1520_ = (!lean_is_exclusive(v_it_1502_)) as u8;
                    if v_isSharedCheck_1520_ == 0 {
                        v_unused_1521_ = lean_ctor_get(v_it_1502_, 0);
                        lean_dec(v_unused_1521_);
                        v___x_1508_ = v_it_1502_;
                        v_isShared_1509_ = v_isSharedCheck_1520_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_upperBound_1506_);
                        lean_dec(v_it_1502_);
                        v___x_1508_ = lean_box(0);
                        v_isShared_1509_ = v_isSharedCheck_1520_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1510_ = lean_ctor_get(v_next_1505_, 0);
                lean_inc_n(v_val_1510_, 2);
                lean_dec_ref_known(v_next_1505_, 1);
                lean_inc(v_upperBound_1506_);
                v___x_1511_ = lean_apply_2(v_inst_1500_, v_val_1510_, v_upperBound_1506_);
                v___x_1512_ = (lean_unbox(v___x_1511_) as u8);
                if v___x_1512_ == 0 {
                    lean_dec(v_val_1510_);
                    lean_del_object(v___x_1508_);
                    lean_dec(v_upperBound_1506_);
                    lean_dec_ref(v_recur_1504_);
                    lean_dec_ref(v_inst_1501_);
                    return v_acc_1503_;
                } else {
                    v_succ_x3f_1513_ = lean_ctor_get(v_inst_1501_, 0);
                    lean_inc_ref(v_succ_x3f_1513_);
                    lean_dec_ref(v_inst_1501_);
                    lean_inc(v_val_1510_);
                    v___x_1514_ = lean_apply_1(v_succ_x3f_1513_, v_val_1510_);
                    if v_isShared_1509_ == 0 {
                        lean_ctor_set(v___x_1508_, 0, v___x_1514_);
                        v___x_1516_ = v___x_1508_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1514_);
                        lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_upperBound_1506_);
                        v___x_1516_ = v_reuseFailAlloc_1519_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1517_ = lean_array_push(v_acc_1503_, v_val_1510_);
                v___x_1518_ = lean_apply_3(v_recur_1504_, v___x_1516_, v___x_1517_, lean_box(0));
                return v___x_1518_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rco_toList___redArg(
    mut v_inst_1522_: *mut LeanObject,
    mut v_inst_1523_: *mut LeanObject,
    mut v_r_1524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1529_: u8 = 0;
    let mut v___f_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1525_ = lean_ctor_get(v_r_1524_, 0);
                v_upper_1526_ = lean_ctor_get(v_r_1524_, 1);
                v_isSharedCheck_1538_ = (!lean_is_exclusive(v_r_1524_)) as u8;
                if v_isSharedCheck_1538_ == 0 {
                    v___x_1528_ = v_r_1524_;
                    v_isShared_1529_ = v_isSharedCheck_1538_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1526_);
                    lean_inc(v_lower_1525_);
                    lean_dec(v_r_1524_);
                    v___x_1528_ = lean_box(0);
                    v_isShared_1529_ = v_isSharedCheck_1538_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1530_ = lean_alloc_closure(
                    l_Std_Rco_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_1530_, 0, v_inst_1522_);
                lean_closure_set(v___f_1530_, 1, v_inst_1523_);
                v___x_1531_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1531_, 0, v_lower_1525_);
                if v_isShared_1529_ == 0 {
                    lean_ctor_set(v___x_1528_, 0, v___x_1531_);
                    v___x_1533_ = v___x_1528_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1531_);
                    lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_upper_1526_);
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
    mut v_00_u03b1_1539_: *mut LeanObject,
    mut v_inst_1540_: *mut LeanObject,
    mut v_inst_1541_: *mut LeanObject,
    mut v_inst_1542_: *mut LeanObject,
    mut v_inst_1543_: *mut LeanObject,
    mut v_inst_1544_: *mut LeanObject,
    mut v_r_1545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1550_: u8 = 0;
    let mut v___f_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1546_ = lean_ctor_get(v_r_1545_, 0);
                v_upper_1547_ = lean_ctor_get(v_r_1545_, 1);
                v_isSharedCheck_1559_ = (!lean_is_exclusive(v_r_1545_)) as u8;
                if v_isSharedCheck_1559_ == 0 {
                    v___x_1549_ = v_r_1545_;
                    v_isShared_1550_ = v_isSharedCheck_1559_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1547_);
                    lean_inc(v_lower_1546_);
                    lean_dec(v_r_1545_);
                    v___x_1549_ = lean_box(0);
                    v_isShared_1550_ = v_isSharedCheck_1559_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1551_ = lean_alloc_closure(
                    l_Std_Rco_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_1551_, 0, v_inst_1541_);
                lean_closure_set(v___f_1551_, 1, v_inst_1542_);
                v___x_1552_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1552_, 0, v_lower_1546_);
                if v_isShared_1550_ == 0 {
                    lean_ctor_set(v___x_1549_, 0, v___x_1552_);
                    v___x_1554_ = v___x_1549_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1552_);
                    lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_upper_1547_);
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
    mut v_inst_1560_: *mut LeanObject,
    mut v_inst_1561_: *mut LeanObject,
    mut v_r_1562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1567_: u8 = 0;
    let mut v___f_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1575_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1563_ = lean_ctor_get(v_r_1562_, 0);
                v_upper_1564_ = lean_ctor_get(v_r_1562_, 1);
                v_isSharedCheck_1575_ = (!lean_is_exclusive(v_r_1562_)) as u8;
                if v_isSharedCheck_1575_ == 0 {
                    v___x_1566_ = v_r_1562_;
                    v_isShared_1567_ = v_isSharedCheck_1575_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1564_);
                    lean_inc(v_lower_1563_);
                    lean_dec(v_r_1562_);
                    v___x_1566_ = lean_box(0);
                    v_isShared_1567_ = v_isSharedCheck_1575_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1568_ = lean_alloc_closure(
                    l_Std_Rco_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_1568_, 0, v_inst_1560_);
                lean_closure_set(v___f_1568_, 1, v_inst_1561_);
                v___x_1569_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1569_, 0, v_lower_1563_);
                if v_isShared_1567_ == 0 {
                    lean_ctor_set(v___x_1566_, 0, v___x_1569_);
                    v___x_1571_ = v___x_1566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1569_);
                    lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_upper_1564_);
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
    mut v_00_u03b1_1576_: *mut LeanObject,
    mut v_inst_1577_: *mut LeanObject,
    mut v_inst_1578_: *mut LeanObject,
    mut v_inst_1579_: *mut LeanObject,
    mut v_inst_1580_: *mut LeanObject,
    mut v_inst_1581_: *mut LeanObject,
    mut v_r_1582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1587_: u8 = 0;
    let mut v___f_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1583_ = lean_ctor_get(v_r_1582_, 0);
                v_upper_1584_ = lean_ctor_get(v_r_1582_, 1);
                v_isSharedCheck_1595_ = (!lean_is_exclusive(v_r_1582_)) as u8;
                if v_isSharedCheck_1595_ == 0 {
                    v___x_1586_ = v_r_1582_;
                    v_isShared_1587_ = v_isSharedCheck_1595_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1584_);
                    lean_inc(v_lower_1583_);
                    lean_dec(v_r_1582_);
                    v___x_1586_ = lean_box(0);
                    v_isShared_1587_ = v_isSharedCheck_1595_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1588_ = lean_alloc_closure(
                    l_Std_Rco_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_1588_, 0, v_inst_1578_);
                lean_closure_set(v___f_1588_, 1, v_inst_1579_);
                v___x_1589_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1589_, 0, v_lower_1583_);
                if v_isShared_1587_ == 0 {
                    lean_ctor_set(v___x_1586_, 0, v___x_1589_);
                    v___x_1591_ = v___x_1586_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1589_);
                    lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_upper_1584_);
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
    mut v_inst_1596_: *mut LeanObject,
    mut v_r_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    v_lower_1598_ = lean_ctor_get(v_r_1597_, 0);
    lean_inc(v_lower_1598_);
    v_upper_1599_ = lean_ctor_get(v_r_1597_, 1);
    lean_inc(v_upper_1599_);
    lean_dec_ref(v_r_1597_);
    v___x_1600_ = lean_apply_2(v_inst_1596_, v_lower_1598_, v_upper_1599_);
    return v___x_1600_;
}
pub unsafe fn l_Std_Rco_size(
    mut v_00_u03b1_1601_: *mut LeanObject,
    mut v_inst_1602_: *mut LeanObject,
    mut v_r_1603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    v_lower_1604_ = lean_ctor_get(v_r_1603_, 0);
    lean_inc(v_lower_1604_);
    v_upper_1605_ = lean_ctor_get(v_r_1603_, 1);
    lean_inc(v_upper_1605_);
    lean_dec_ref(v_r_1603_);
    v___x_1606_ = lean_apply_2(v_inst_1602_, v_lower_1604_, v_upper_1605_);
    return v___x_1606_;
}
pub unsafe fn l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3(
    mut v_inst_1607_: *mut LeanObject,
    mut v_inst_1608_: *mut LeanObject,
    mut v_inst_1609_: *mut LeanObject,
    mut v_00_u03b2_1610_: *mut LeanObject,
    mut v_r_1611_: *mut LeanObject,
    mut v_init_1612_: *mut LeanObject,
    mut v_f_1613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1614_ = lean_ctor_get(v_inst_1607_, 0);
    lean_inc_ref(v_toApplicative_1614_);
    v_lower_1615_ = lean_ctor_get(v_r_1611_, 0);
    lean_inc(v_lower_1615_);
    v_upper_1616_ = lean_ctor_get(v_r_1611_, 1);
    lean_inc(v_upper_1616_);
    lean_dec_ref(v_r_1611_);
    v_toBind_1617_ = lean_ctor_get(v_inst_1607_, 1);
    lean_inc(v_toBind_1617_);
    lean_dec_ref(v_inst_1607_);
    v_toPure_1618_ = lean_ctor_get(v_toApplicative_1614_, 1);
    lean_inc_n(v_toPure_1618_, 2);
    lean_dec_ref(v_toApplicative_1614_);
    v___f_1619_ = lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_1619_, 0, v_toPure_1618_);
    v___f_1620_ = lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2 as *mut core::ffi::c_void, 11, 7);
    lean_closure_set(v___f_1620_, 0, v_inst_1608_);
    lean_closure_set(v___f_1620_, 1, v_upper_1616_);
    lean_closure_set(v___f_1620_, 2, v_toPure_1618_);
    lean_closure_set(v___f_1620_, 3, v_inst_1609_);
    lean_closure_set(v___f_1620_, 4, v_f_1613_);
    lean_closure_set(v___f_1620_, 5, v_toBind_1617_);
    lean_closure_set(v___f_1620_, 6, v___f_1619_);
    v___x_1621_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1620_,
        v_lower_1615_,
        v_init_1612_,
        lean_box(0),
    );
    return v___x_1621_;
}
pub unsafe fn l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_1622_: *mut LeanObject,
    mut v_inst_1623_: *mut LeanObject,
    mut v_inst_1624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1625_: *mut LeanObject = core::ptr::null_mut();
    v___f_1625_ = lean_alloc_closure(l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3 as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___f_1625_, 0, v_inst_1624_);
    lean_closure_set(v___f_1625_, 1, v_inst_1623_);
    lean_closure_set(v___f_1625_, 2, v_inst_1622_);
    return v___f_1625_;
}
pub unsafe fn l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_1626_: *mut LeanObject,
    mut v_m_1627_: *mut LeanObject,
    mut v_inst_1628_: *mut LeanObject,
    mut v_inst_1629_: *mut LeanObject,
    mut v_inst_1630_: *mut LeanObject,
    mut v_inst_1631_: *mut LeanObject,
    mut v_inst_1632_: *mut LeanObject,
    mut v_inst_1633_: *mut LeanObject,
    mut v_inst_1634_: *mut LeanObject,
    mut v_inst_1635_: *mut LeanObject,
    mut v_inst_1636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1637_: *mut LeanObject = core::ptr::null_mut();
    v___f_1637_ = lean_alloc_closure(l_Std_Rco_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3 as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___f_1637_, 0, v_inst_1635_);
    lean_closure_set(v___f_1637_, 1, v_inst_1631_);
    lean_closure_set(v___f_1637_, 2, v_inst_1628_);
    return v___f_1637_;
}
pub unsafe fn l_Std_Rci_Internal_iter___redArg(mut v_r_1638_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    v___x_1639_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1639_, 0, v_r_1638_);
    return v___x_1639_;
}
pub unsafe fn l_Std_Rci_Internal_iter(
    mut v_00_u03b1_1640_: *mut LeanObject,
    mut v_inst_1641_: *mut LeanObject,
    mut v_r_1642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    v___x_1643_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1643_, 0, v_r_1642_);
    return v___x_1643_;
}
pub unsafe fn l_Std_Rci_Internal_iter___boxed(
    mut v_00_u03b1_1644_: *mut LeanObject,
    mut v_inst_1645_: *mut LeanObject,
    mut v_r_1646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1647_: *mut LeanObject = core::ptr::null_mut();
    v_res_1647_ = l_Std_Rci_Internal_iter(v_00_u03b1_1644_, v_inst_1645_, v_r_1646_);
    lean_dec_ref(v_inst_1645_);
    return v_res_1647_;
}
pub unsafe fn l_Std_Rci_toList___redArg___lam__0(
    mut v_inst_1648_: *mut LeanObject,
    mut v_it_1649_: *mut LeanObject,
    mut v_acc_1650_: *mut LeanObject,
    mut v_recur_1651_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_1649_) == 0 {
        lean_dec_ref(v_recur_1651_);
        lean_dec_ref(v_inst_1648_);
        return v_acc_1650_;
    } else {
        let mut v_val_1652_: *mut LeanObject = core::ptr::null_mut();
        let mut v_succ_x3f_1653_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
        v_val_1652_ = lean_ctor_get(v_it_1649_, 0);
        lean_inc_n(v_val_1652_, 2);
        lean_dec_ref_known(v_it_1649_, 1);
        v_succ_x3f_1653_ = lean_ctor_get(v_inst_1648_, 0);
        lean_inc_ref(v_succ_x3f_1653_);
        lean_dec_ref(v_inst_1648_);
        v___x_1654_ = lean_apply_1(v_succ_x3f_1653_, v_val_1652_);
        v___x_1655_ = lean_array_push(v_acc_1650_, v_val_1652_);
        v___x_1656_ = lean_apply_3(v_recur_1651_, v___x_1654_, v___x_1655_, lean_box(0));
        return v___x_1656_;
    }
}
pub unsafe fn l_Std_Rci_toList___redArg(
    mut v_inst_1657_: *mut LeanObject,
    mut v_r_1658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    v___f_1659_ = lean_alloc_closure(
        l_Std_Rci_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1659_, 0, v_inst_1657_);
    v___x_1660_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1660_, 0, v_r_1658_);
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
    mut v_00_u03b1_1664_: *mut LeanObject,
    mut v_inst_1665_: *mut LeanObject,
    mut v_inst_1666_: *mut LeanObject,
    mut v_inst_1667_: *mut LeanObject,
    mut v_r_1668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    v___f_1669_ = lean_alloc_closure(
        l_Std_Rci_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1669_, 0, v_inst_1665_);
    v___x_1670_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1670_, 0, v_r_1668_);
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
    mut v_inst_1674_: *mut LeanObject,
    mut v_r_1675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    v___f_1676_ = lean_alloc_closure(
        l_Std_Rci_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1676_, 0, v_inst_1674_);
    v___x_1677_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1677_, 0, v_r_1675_);
    v___x_1678_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_1679_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_1676_,
        v___x_1677_,
        v___x_1678_,
    );
    return v___x_1679_;
}
pub unsafe fn l_Std_Rci_toArray(
    mut v_00_u03b1_1680_: *mut LeanObject,
    mut v_inst_1681_: *mut LeanObject,
    mut v_inst_1682_: *mut LeanObject,
    mut v_inst_1683_: *mut LeanObject,
    mut v_r_1684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    v___f_1685_ = lean_alloc_closure(
        l_Std_Rci_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1685_, 0, v_inst_1681_);
    v___x_1686_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1686_, 0, v_r_1684_);
    v___x_1687_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_1688_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_1685_,
        v___x_1686_,
        v___x_1687_,
    );
    return v___x_1688_;
}
pub unsafe fn l_Std_Rci_size___redArg(
    mut v_inst_1689_: *mut LeanObject,
    mut v_r_1690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    v___x_1691_ = lean_apply_1(v_inst_1689_, v_r_1690_);
    return v___x_1691_;
}
pub unsafe fn l_Std_Rci_size(
    mut v_00_u03b1_1692_: *mut LeanObject,
    mut v_inst_1693_: *mut LeanObject,
    mut v_r_1694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    v___x_1695_ = lean_apply_1(v_inst_1693_, v_r_1694_);
    return v___x_1695_;
}
pub unsafe fn l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2(
    mut v_toPure_1696_: *mut LeanObject,
    mut v_inst_1697_: *mut LeanObject,
    mut v_f_1698_: *mut LeanObject,
    mut v_toBind_1699_: *mut LeanObject,
    mut v___f_1700_: *mut LeanObject,
    mut v_next_1701_: *mut LeanObject,
    mut v_acc_1702_: *mut LeanObject,
    mut v_h_1703_: *mut LeanObject,
    mut v_G_1704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_next_1701_);
    v___f_1705_ = lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__1 as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___f_1705_, 0, v_toPure_1696_);
    lean_closure_set(v___f_1705_, 1, v_inst_1697_);
    lean_closure_set(v___f_1705_, 2, v_next_1701_);
    lean_closure_set(v___f_1705_, 3, v_G_1704_);
    v___x_1706_ = lean_apply_3(v_f_1698_, v_next_1701_, lean_box(0), v_acc_1702_);
    lean_inc(v_toBind_1699_);
    v___x_1707_ = lean_apply_4(
        v_toBind_1699_,
        lean_box(0),
        lean_box(0),
        v___x_1706_,
        v___f_1700_,
    );
    v___x_1708_ = lean_apply_4(
        v_toBind_1699_,
        lean_box(0),
        lean_box(0),
        v___x_1707_,
        v___f_1705_,
    );
    return v___x_1708_;
}
pub unsafe fn l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0(
    mut v_inst_1709_: *mut LeanObject,
    mut v_inst_1710_: *mut LeanObject,
    mut v_00_u03b2_1711_: *mut LeanObject,
    mut v_r_1712_: *mut LeanObject,
    mut v_init_1713_: *mut LeanObject,
    mut v_f_1714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1715_ = lean_ctor_get(v_inst_1709_, 0);
    lean_inc_ref(v_toApplicative_1715_);
    v_toBind_1716_ = lean_ctor_get(v_inst_1709_, 1);
    lean_inc(v_toBind_1716_);
    lean_dec_ref(v_inst_1709_);
    v_toPure_1717_ = lean_ctor_get(v_toApplicative_1715_, 1);
    lean_inc_n(v_toPure_1717_, 2);
    lean_dec_ref(v_toApplicative_1715_);
    v___f_1718_ = lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_1718_, 0, v_toPure_1717_);
    v___f_1719_ = lean_alloc_closure(l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2 as *mut core::ffi::c_void, 9, 5);
    lean_closure_set(v___f_1719_, 0, v_toPure_1717_);
    lean_closure_set(v___f_1719_, 1, v_inst_1710_);
    lean_closure_set(v___f_1719_, 2, v_f_1714_);
    lean_closure_set(v___f_1719_, 3, v_toBind_1716_);
    lean_closure_set(v___f_1719_, 4, v___f_1718_);
    v___x_1720_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1719_, v_r_1712_, v_init_1713_, lean_box(0));
    return v___x_1720_;
}
pub unsafe fn l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_1721_: *mut LeanObject,
    mut v_inst_1722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1723_: *mut LeanObject = core::ptr::null_mut();
    v___f_1723_ = lean_alloc_closure(l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 6, 2);
    lean_closure_set(v___f_1723_, 0, v_inst_1722_);
    lean_closure_set(v___f_1723_, 1, v_inst_1721_);
    return v___f_1723_;
}
pub unsafe fn l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_1724_: *mut LeanObject,
    mut v_m_1725_: *mut LeanObject,
    mut v_inst_1726_: *mut LeanObject,
    mut v_inst_1727_: *mut LeanObject,
    mut v_inst_1728_: *mut LeanObject,
    mut v_inst_1729_: *mut LeanObject,
    mut v_inst_1730_: *mut LeanObject,
    mut v_inst_1731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1732_: *mut LeanObject = core::ptr::null_mut();
    v___f_1732_ = lean_alloc_closure(l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 6, 2);
    lean_closure_set(v___f_1732_, 0, v_inst_1730_);
    lean_closure_set(v___f_1732_, 1, v_inst_1726_);
    return v___f_1732_;
}
pub unsafe fn l_Std_Roc_Internal_iter___redArg(
    mut v_inst_1733_: *mut LeanObject,
    mut v_r_1734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1735_ = lean_ctor_get(v_inst_1733_, 0);
                lean_inc_ref(v_succ_x3f_1735_);
                lean_dec_ref(v_inst_1733_);
                v_lower_1736_ = lean_ctor_get(v_r_1734_, 0);
                v_upper_1737_ = lean_ctor_get(v_r_1734_, 1);
                v_isSharedCheck_1745_ = (!lean_is_exclusive(v_r_1734_)) as u8;
                if v_isSharedCheck_1745_ == 0 {
                    v___x_1739_ = v_r_1734_;
                    v_isShared_1740_ = v_isSharedCheck_1745_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1737_);
                    lean_inc(v_lower_1736_);
                    lean_dec(v_r_1734_);
                    v___x_1739_ = lean_box(0);
                    v_isShared_1740_ = v_isSharedCheck_1745_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1741_ = lean_apply_1(v_succ_x3f_1735_, v_lower_1736_);
                if v_isShared_1740_ == 0 {
                    lean_ctor_set(v___x_1739_, 0, v___x_1741_);
                    v___x_1743_ = v___x_1739_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
                    lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_upper_1737_);
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
    mut v_00_u03b1_1746_: *mut LeanObject,
    mut v_inst_1747_: *mut LeanObject,
    mut v_r_1748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1754_: u8 = 0;
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1749_ = lean_ctor_get(v_inst_1747_, 0);
                lean_inc_ref(v_succ_x3f_1749_);
                lean_dec_ref(v_inst_1747_);
                v_lower_1750_ = lean_ctor_get(v_r_1748_, 0);
                v_upper_1751_ = lean_ctor_get(v_r_1748_, 1);
                v_isSharedCheck_1759_ = (!lean_is_exclusive(v_r_1748_)) as u8;
                if v_isSharedCheck_1759_ == 0 {
                    v___x_1753_ = v_r_1748_;
                    v_isShared_1754_ = v_isSharedCheck_1759_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1751_);
                    lean_inc(v_lower_1750_);
                    lean_dec(v_r_1748_);
                    v___x_1753_ = lean_box(0);
                    v_isShared_1754_ = v_isSharedCheck_1759_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1755_ = lean_apply_1(v_succ_x3f_1749_, v_lower_1750_);
                if v_isShared_1754_ == 0 {
                    lean_ctor_set(v___x_1753_, 0, v___x_1755_);
                    v___x_1757_ = v___x_1753_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
                    lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_upper_1751_);
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
    mut v_inst_1760_: *mut LeanObject,
    mut v_succ_x3f_1761_: *mut LeanObject,
    mut v_it_1762_: *mut LeanObject,
    mut v_acc_1763_: *mut LeanObject,
    mut v_recur_1764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1769_: u8 = 0;
    let mut v_val_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: u8 = 0;
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1779_: u8 = 0;
    let mut v_unused_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1765_ = lean_ctor_get(v_it_1762_, 0);
                lean_inc(v_next_1765_);
                if lean_obj_tag(v_next_1765_) == 0 {
                    lean_dec_ref(v_recur_1764_);
                    lean_dec_ref(v_it_1762_);
                    lean_dec_ref(v_succ_x3f_1761_);
                    lean_dec_ref(v_inst_1760_);
                    return v_acc_1763_;
                } else {
                    v_upperBound_1766_ = lean_ctor_get(v_it_1762_, 1);
                    v_isSharedCheck_1779_ = (!lean_is_exclusive(v_it_1762_)) as u8;
                    if v_isSharedCheck_1779_ == 0 {
                        v_unused_1780_ = lean_ctor_get(v_it_1762_, 0);
                        lean_dec(v_unused_1780_);
                        v___x_1768_ = v_it_1762_;
                        v_isShared_1769_ = v_isSharedCheck_1779_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_upperBound_1766_);
                        lean_dec(v_it_1762_);
                        v___x_1768_ = lean_box(0);
                        v_isShared_1769_ = v_isSharedCheck_1779_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1770_ = lean_ctor_get(v_next_1765_, 0);
                lean_inc_n(v_val_1770_, 2);
                lean_dec_ref_known(v_next_1765_, 1);
                lean_inc(v_upperBound_1766_);
                v___x_1771_ = lean_apply_2(v_inst_1760_, v_val_1770_, v_upperBound_1766_);
                v___x_1772_ = (lean_unbox(v___x_1771_) as u8);
                if v___x_1772_ == 0 {
                    lean_dec(v_val_1770_);
                    lean_del_object(v___x_1768_);
                    lean_dec(v_upperBound_1766_);
                    lean_dec_ref(v_recur_1764_);
                    lean_dec_ref(v_succ_x3f_1761_);
                    return v_acc_1763_;
                } else {
                    lean_inc(v_val_1770_);
                    v___x_1773_ = lean_apply_1(v_succ_x3f_1761_, v_val_1770_);
                    if v_isShared_1769_ == 0 {
                        lean_ctor_set(v___x_1768_, 0, v___x_1773_);
                        v___x_1775_ = v___x_1768_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1773_);
                        lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_upperBound_1766_);
                        v___x_1775_ = v_reuseFailAlloc_1778_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1776_ = lean_array_push(v_acc_1763_, v_val_1770_);
                v___x_1777_ = lean_apply_3(v_recur_1764_, v___x_1775_, v___x_1776_, lean_box(0));
                return v___x_1777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roc_toList___redArg(
    mut v_inst_1781_: *mut LeanObject,
    mut v_inst_1782_: *mut LeanObject,
    mut v_r_1783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1789_: u8 = 0;
    let mut v___f_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1784_ = lean_ctor_get(v_inst_1782_, 0);
                lean_inc_ref(v_succ_x3f_1784_);
                lean_dec_ref(v_inst_1782_);
                v_lower_1785_ = lean_ctor_get(v_r_1783_, 0);
                v_upper_1786_ = lean_ctor_get(v_r_1783_, 1);
                v_isSharedCheck_1798_ = (!lean_is_exclusive(v_r_1783_)) as u8;
                if v_isSharedCheck_1798_ == 0 {
                    v___x_1788_ = v_r_1783_;
                    v_isShared_1789_ = v_isSharedCheck_1798_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1786_);
                    lean_inc(v_lower_1785_);
                    lean_dec(v_r_1783_);
                    v___x_1788_ = lean_box(0);
                    v_isShared_1789_ = v_isSharedCheck_1798_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_succ_x3f_1784_);
                v___f_1790_ = lean_alloc_closure(
                    l_Std_Roc_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_1790_, 0, v_inst_1781_);
                lean_closure_set(v___f_1790_, 1, v_succ_x3f_1784_);
                v___x_1791_ = lean_apply_1(v_succ_x3f_1784_, v_lower_1785_);
                if v_isShared_1789_ == 0 {
                    lean_ctor_set(v___x_1788_, 0, v___x_1791_);
                    v___x_1793_ = v___x_1788_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1791_);
                    lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_upper_1786_);
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
    mut v_00_u03b1_1799_: *mut LeanObject,
    mut v_inst_1800_: *mut LeanObject,
    mut v_inst_1801_: *mut LeanObject,
    mut v_inst_1802_: *mut LeanObject,
    mut v_inst_1803_: *mut LeanObject,
    mut v_inst_1804_: *mut LeanObject,
    mut v_r_1805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1811_: u8 = 0;
    let mut v___f_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1806_ = lean_ctor_get(v_inst_1802_, 0);
                lean_inc_ref(v_succ_x3f_1806_);
                lean_dec_ref(v_inst_1802_);
                v_lower_1807_ = lean_ctor_get(v_r_1805_, 0);
                v_upper_1808_ = lean_ctor_get(v_r_1805_, 1);
                v_isSharedCheck_1820_ = (!lean_is_exclusive(v_r_1805_)) as u8;
                if v_isSharedCheck_1820_ == 0 {
                    v___x_1810_ = v_r_1805_;
                    v_isShared_1811_ = v_isSharedCheck_1820_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1808_);
                    lean_inc(v_lower_1807_);
                    lean_dec(v_r_1805_);
                    v___x_1810_ = lean_box(0);
                    v_isShared_1811_ = v_isSharedCheck_1820_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_succ_x3f_1806_);
                v___f_1812_ = lean_alloc_closure(
                    l_Std_Roc_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_1812_, 0, v_inst_1801_);
                lean_closure_set(v___f_1812_, 1, v_succ_x3f_1806_);
                v___x_1813_ = lean_apply_1(v_succ_x3f_1806_, v_lower_1807_);
                if v_isShared_1811_ == 0 {
                    lean_ctor_set(v___x_1810_, 0, v___x_1813_);
                    v___x_1815_ = v___x_1810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1813_);
                    lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_upper_1808_);
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
    mut v_inst_1821_: *mut LeanObject,
    mut v_inst_1822_: *mut LeanObject,
    mut v_r_1823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1829_: u8 = 0;
    let mut v___f_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1837_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1824_ = lean_ctor_get(v_inst_1822_, 0);
                lean_inc_ref(v_succ_x3f_1824_);
                lean_dec_ref(v_inst_1822_);
                v_lower_1825_ = lean_ctor_get(v_r_1823_, 0);
                v_upper_1826_ = lean_ctor_get(v_r_1823_, 1);
                v_isSharedCheck_1837_ = (!lean_is_exclusive(v_r_1823_)) as u8;
                if v_isSharedCheck_1837_ == 0 {
                    v___x_1828_ = v_r_1823_;
                    v_isShared_1829_ = v_isSharedCheck_1837_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1826_);
                    lean_inc(v_lower_1825_);
                    lean_dec(v_r_1823_);
                    v___x_1828_ = lean_box(0);
                    v_isShared_1829_ = v_isSharedCheck_1837_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_succ_x3f_1824_);
                v___f_1830_ = lean_alloc_closure(
                    l_Std_Roc_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_1830_, 0, v_inst_1821_);
                lean_closure_set(v___f_1830_, 1, v_succ_x3f_1824_);
                v___x_1831_ = lean_apply_1(v_succ_x3f_1824_, v_lower_1825_);
                if v_isShared_1829_ == 0 {
                    lean_ctor_set(v___x_1828_, 0, v___x_1831_);
                    v___x_1833_ = v___x_1828_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1831_);
                    lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_upper_1826_);
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
    mut v_00_u03b1_1838_: *mut LeanObject,
    mut v_inst_1839_: *mut LeanObject,
    mut v_inst_1840_: *mut LeanObject,
    mut v_inst_1841_: *mut LeanObject,
    mut v_inst_1842_: *mut LeanObject,
    mut v_inst_1843_: *mut LeanObject,
    mut v_r_1844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1850_: u8 = 0;
    let mut v___f_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1845_ = lean_ctor_get(v_inst_1841_, 0);
                lean_inc_ref(v_succ_x3f_1845_);
                lean_dec_ref(v_inst_1841_);
                v_lower_1846_ = lean_ctor_get(v_r_1844_, 0);
                v_upper_1847_ = lean_ctor_get(v_r_1844_, 1);
                v_isSharedCheck_1858_ = (!lean_is_exclusive(v_r_1844_)) as u8;
                if v_isSharedCheck_1858_ == 0 {
                    v___x_1849_ = v_r_1844_;
                    v_isShared_1850_ = v_isSharedCheck_1858_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1847_);
                    lean_inc(v_lower_1846_);
                    lean_dec(v_r_1844_);
                    v___x_1849_ = lean_box(0);
                    v_isShared_1850_ = v_isSharedCheck_1858_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_succ_x3f_1845_);
                v___f_1851_ = lean_alloc_closure(
                    l_Std_Roc_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_1851_, 0, v_inst_1840_);
                lean_closure_set(v___f_1851_, 1, v_succ_x3f_1845_);
                v___x_1852_ = lean_apply_1(v_succ_x3f_1845_, v_lower_1846_);
                if v_isShared_1850_ == 0 {
                    lean_ctor_set(v___x_1849_, 0, v___x_1852_);
                    v___x_1854_ = v___x_1849_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1852_);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_upper_1847_);
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
    mut v_inst_1859_: *mut LeanObject,
    mut v_inst_1860_: *mut LeanObject,
    mut v_r_1861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_1862_ = lean_ctor_get(v_inst_1860_, 0);
    lean_inc_ref(v_succ_x3f_1862_);
    lean_dec_ref(v_inst_1860_);
    v_lower_1863_ = lean_ctor_get(v_r_1861_, 0);
    lean_inc(v_lower_1863_);
    v_upper_1864_ = lean_ctor_get(v_r_1861_, 1);
    lean_inc(v_upper_1864_);
    lean_dec_ref(v_r_1861_);
    v___x_1865_ = lean_apply_1(v_succ_x3f_1862_, v_lower_1863_);
    if lean_obj_tag(v___x_1865_) == 0 {
        let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_upper_1864_);
        lean_dec_ref(v_inst_1859_);
        v___x_1866_ = lean_unsigned_to_nat(0);
        return v___x_1866_;
    } else {
        let mut v_val_1867_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
        v_val_1867_ = lean_ctor_get(v___x_1865_, 0);
        lean_inc(v_val_1867_);
        lean_dec_ref_known(v___x_1865_, 1);
        v___x_1868_ = lean_apply_2(v_inst_1859_, v_val_1867_, v_upper_1864_);
        return v___x_1868_;
    }
}
pub unsafe fn l_Std_Roc_size(
    mut v_00_u03b1_1869_: *mut LeanObject,
    mut v_inst_1870_: *mut LeanObject,
    mut v_inst_1871_: *mut LeanObject,
    mut v_r_1872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_1873_ = lean_ctor_get(v_inst_1871_, 0);
    lean_inc_ref(v_succ_x3f_1873_);
    lean_dec_ref(v_inst_1871_);
    v_lower_1874_ = lean_ctor_get(v_r_1872_, 0);
    lean_inc(v_lower_1874_);
    v_upper_1875_ = lean_ctor_get(v_r_1872_, 1);
    lean_inc(v_upper_1875_);
    lean_dec_ref(v_r_1872_);
    v___x_1876_ = lean_apply_1(v_succ_x3f_1873_, v_lower_1874_);
    if lean_obj_tag(v___x_1876_) == 0 {
        let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_upper_1875_);
        lean_dec_ref(v_inst_1870_);
        v___x_1877_ = lean_unsigned_to_nat(0);
        return v___x_1877_;
    } else {
        let mut v_val_1878_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
        v_val_1878_ = lean_ctor_get(v___x_1876_, 0);
        lean_inc(v_val_1878_);
        lean_dec_ref_known(v___x_1876_, 1);
        v___x_1879_ = lean_apply_2(v_inst_1870_, v_val_1878_, v_upper_1875_);
        return v___x_1879_;
    }
}
pub unsafe fn l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__1(
    mut v_toPure_1880_: *mut LeanObject,
    mut v_succ_x3f_1881_: *mut LeanObject,
    mut v_next_1882_: *mut LeanObject,
    mut v_G_1883_: *mut LeanObject,
    mut v_____do__lift_1884_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1884_) == 0 {
        let mut v_a_1885_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_G_1883_);
        lean_dec(v_next_1882_);
        lean_dec_ref(v_succ_x3f_1881_);
        v_a_1885_ = lean_ctor_get(v_____do__lift_1884_, 0);
        lean_inc(v_a_1885_);
        lean_dec_ref_known(v_____do__lift_1884_, 1);
        v___x_1886_ = lean_apply_2(v_toPure_1880_, lean_box(0), v_a_1885_);
        return v___x_1886_;
    } else {
        let mut v_a_1887_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
        v_a_1887_ = lean_ctor_get(v_____do__lift_1884_, 0);
        lean_inc(v_a_1887_);
        lean_dec_ref_known(v_____do__lift_1884_, 1);
        v___x_1888_ = lean_apply_1(v_succ_x3f_1881_, v_next_1882_);
        if lean_obj_tag(v___x_1888_) == 0 {
            let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_G_1883_);
            v___x_1889_ = lean_apply_2(v_toPure_1880_, lean_box(0), v_a_1887_);
            return v___x_1889_;
        } else {
            let mut v_val_1890_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toPure_1880_);
            v_val_1890_ = lean_ctor_get(v___x_1888_, 0);
            lean_inc(v_val_1890_);
            lean_dec_ref_known(v___x_1888_, 1);
            v___x_1891_ = lean_apply_4(v_G_1883_, v_val_1890_, v_a_1887_, lean_box(0), lean_box(0));
            return v___x_1891_;
        }
    }
}
pub unsafe fn l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0(
    mut v_inst_1892_: *mut LeanObject,
    mut v_upper_1893_: *mut LeanObject,
    mut v_toPure_1894_: *mut LeanObject,
    mut v_succ_x3f_1895_: *mut LeanObject,
    mut v_f_1896_: *mut LeanObject,
    mut v_toBind_1897_: *mut LeanObject,
    mut v___f_1898_: *mut LeanObject,
    mut v_next_1899_: *mut LeanObject,
    mut v_acc_1900_: *mut LeanObject,
    mut v_h_1901_: *mut LeanObject,
    mut v_G_1902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: u8 = 0;
    lean_inc(v_next_1899_);
    v___x_1903_ = lean_apply_2(v_inst_1892_, v_next_1899_, v_upper_1893_);
    v___x_1904_ = (lean_unbox(v___x_1903_) as u8);
    if v___x_1904_ == 0 {
        let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_G_1902_);
        lean_dec(v_next_1899_);
        lean_dec(v___f_1898_);
        lean_dec(v_toBind_1897_);
        lean_dec(v_f_1896_);
        lean_dec_ref(v_succ_x3f_1895_);
        v___x_1905_ = lean_apply_2(v_toPure_1894_, lean_box(0), v_acc_1900_);
        return v___x_1905_;
    } else {
        let mut v___f_1906_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_next_1899_);
        v___f_1906_ = lean_alloc_closure(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__1 as *mut core::ffi::c_void, 5, 4);
        lean_closure_set(v___f_1906_, 0, v_toPure_1894_);
        lean_closure_set(v___f_1906_, 1, v_succ_x3f_1895_);
        lean_closure_set(v___f_1906_, 2, v_next_1899_);
        lean_closure_set(v___f_1906_, 3, v_G_1902_);
        v___x_1907_ = lean_apply_3(v_f_1896_, v_next_1899_, lean_box(0), v_acc_1900_);
        lean_inc(v_toBind_1897_);
        v___x_1908_ = lean_apply_4(
            v_toBind_1897_,
            lean_box(0),
            lean_box(0),
            v___x_1907_,
            v___f_1898_,
        );
        v___x_1909_ = lean_apply_4(
            v_toBind_1897_,
            lean_box(0),
            lean_box(0),
            v___x_1908_,
            v___f_1906_,
        );
        return v___x_1909_;
    }
}
pub unsafe fn l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2(
    mut v_inst_1910_: *mut LeanObject,
    mut v_inst_1911_: *mut LeanObject,
    mut v_inst_1912_: *mut LeanObject,
    mut v_00_u03b2_1913_: *mut LeanObject,
    mut v_r_1914_: *mut LeanObject,
    mut v_init_1915_: *mut LeanObject,
    mut v_f_1916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1917_ = lean_ctor_get(v_inst_1911_, 0);
    lean_inc_ref(v_toApplicative_1917_);
    v_succ_x3f_1918_ = lean_ctor_get(v_inst_1910_, 0);
    lean_inc_ref_n(v_succ_x3f_1918_, 2);
    lean_dec_ref(v_inst_1910_);
    v_lower_1919_ = lean_ctor_get(v_r_1914_, 0);
    lean_inc(v_lower_1919_);
    v_upper_1920_ = lean_ctor_get(v_r_1914_, 1);
    lean_inc(v_upper_1920_);
    lean_dec_ref(v_r_1914_);
    v_toBind_1921_ = lean_ctor_get(v_inst_1911_, 1);
    lean_inc(v_toBind_1921_);
    lean_dec_ref(v_inst_1911_);
    v_toPure_1922_ = lean_ctor_get(v_toApplicative_1917_, 1);
    lean_inc(v_toPure_1922_);
    lean_dec_ref(v_toApplicative_1917_);
    v___x_1923_ = lean_apply_1(v_succ_x3f_1918_, v_lower_1919_);
    if lean_obj_tag(v___x_1923_) == 0 {
        let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_1921_);
        lean_dec(v_upper_1920_);
        lean_dec_ref(v_succ_x3f_1918_);
        lean_dec(v_f_1916_);
        lean_dec_ref(v_inst_1912_);
        v___x_1924_ = lean_apply_2(v_toPure_1922_, lean_box(0), v_init_1915_);
        return v___x_1924_;
    } else {
        let mut v_val_1925_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1926_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1927_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
        v_val_1925_ = lean_ctor_get(v___x_1923_, 0);
        lean_inc(v_val_1925_);
        lean_dec_ref_known(v___x_1923_, 1);
        lean_inc(v_toPure_1922_);
        v___f_1926_ = lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
        lean_closure_set(v___f_1926_, 0, v_toPure_1922_);
        v___f_1927_ = lean_alloc_closure(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 11, 7);
        lean_closure_set(v___f_1927_, 0, v_inst_1912_);
        lean_closure_set(v___f_1927_, 1, v_upper_1920_);
        lean_closure_set(v___f_1927_, 2, v_toPure_1922_);
        lean_closure_set(v___f_1927_, 3, v_succ_x3f_1918_);
        lean_closure_set(v___f_1927_, 4, v_f_1916_);
        lean_closure_set(v___f_1927_, 5, v_toBind_1921_);
        lean_closure_set(v___f_1927_, 6, v___f_1926_);
        v___x_1928_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_1927_,
            v_val_1925_,
            v_init_1915_,
            lean_box(0),
        );
        return v___x_1928_;
    }
}
pub unsafe fn l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_1929_: *mut LeanObject,
    mut v_inst_1930_: *mut LeanObject,
    mut v_inst_1931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1932_: *mut LeanObject = core::ptr::null_mut();
    v___f_1932_ = lean_alloc_closure(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2 as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___f_1932_, 0, v_inst_1929_);
    lean_closure_set(v___f_1932_, 1, v_inst_1931_);
    lean_closure_set(v___f_1932_, 2, v_inst_1930_);
    return v___f_1932_;
}
pub unsafe fn l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_1933_: *mut LeanObject,
    mut v_m_1934_: *mut LeanObject,
    mut v_inst_1935_: *mut LeanObject,
    mut v_inst_1936_: *mut LeanObject,
    mut v_inst_1937_: *mut LeanObject,
    mut v_inst_1938_: *mut LeanObject,
    mut v_inst_1939_: *mut LeanObject,
    mut v_inst_1940_: *mut LeanObject,
    mut v_inst_1941_: *mut LeanObject,
    mut v_inst_1942_: *mut LeanObject,
    mut v_inst_1943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1944_: *mut LeanObject = core::ptr::null_mut();
    v___f_1944_ = lean_alloc_closure(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2 as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___f_1944_, 0, v_inst_1935_);
    lean_closure_set(v___f_1944_, 1, v_inst_1942_);
    lean_closure_set(v___f_1944_, 2, v_inst_1937_);
    return v___f_1944_;
}
pub unsafe fn l_Std_Roo_Internal_iter___redArg(
    mut v_inst_1945_: *mut LeanObject,
    mut v_r_1946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1952_: u8 = 0;
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1957_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1947_ = lean_ctor_get(v_inst_1945_, 0);
                lean_inc_ref(v_succ_x3f_1947_);
                lean_dec_ref(v_inst_1945_);
                v_lower_1948_ = lean_ctor_get(v_r_1946_, 0);
                v_upper_1949_ = lean_ctor_get(v_r_1946_, 1);
                v_isSharedCheck_1957_ = (!lean_is_exclusive(v_r_1946_)) as u8;
                if v_isSharedCheck_1957_ == 0 {
                    v___x_1951_ = v_r_1946_;
                    v_isShared_1952_ = v_isSharedCheck_1957_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1949_);
                    lean_inc(v_lower_1948_);
                    lean_dec(v_r_1946_);
                    v___x_1951_ = lean_box(0);
                    v_isShared_1952_ = v_isSharedCheck_1957_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1953_ = lean_apply_1(v_succ_x3f_1947_, v_lower_1948_);
                if v_isShared_1952_ == 0 {
                    lean_ctor_set(v___x_1951_, 0, v___x_1953_);
                    v___x_1955_ = v___x_1951_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
                    lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_upper_1949_);
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
    mut v_00_u03b1_1958_: *mut LeanObject,
    mut v_inst_1959_: *mut LeanObject,
    mut v_r_1960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1966_: u8 = 0;
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1961_ = lean_ctor_get(v_inst_1959_, 0);
                lean_inc_ref(v_succ_x3f_1961_);
                lean_dec_ref(v_inst_1959_);
                v_lower_1962_ = lean_ctor_get(v_r_1960_, 0);
                v_upper_1963_ = lean_ctor_get(v_r_1960_, 1);
                v_isSharedCheck_1971_ = (!lean_is_exclusive(v_r_1960_)) as u8;
                if v_isSharedCheck_1971_ == 0 {
                    v___x_1965_ = v_r_1960_;
                    v_isShared_1966_ = v_isSharedCheck_1971_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1963_);
                    lean_inc(v_lower_1962_);
                    lean_dec(v_r_1960_);
                    v___x_1965_ = lean_box(0);
                    v_isShared_1966_ = v_isSharedCheck_1971_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1967_ = lean_apply_1(v_succ_x3f_1961_, v_lower_1962_);
                if v_isShared_1966_ == 0 {
                    lean_ctor_set(v___x_1965_, 0, v___x_1967_);
                    v___x_1969_ = v___x_1965_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1967_);
                    lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_upper_1963_);
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
    mut v_inst_1972_: *mut LeanObject,
    mut v_succ_x3f_1973_: *mut LeanObject,
    mut v_it_1974_: *mut LeanObject,
    mut v_acc_1975_: *mut LeanObject,
    mut v_recur_1976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v_val_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: u8 = 0;
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v_unused_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1977_ = lean_ctor_get(v_it_1974_, 0);
                lean_inc(v_next_1977_);
                if lean_obj_tag(v_next_1977_) == 0 {
                    lean_dec_ref(v_recur_1976_);
                    lean_dec_ref(v_it_1974_);
                    lean_dec_ref(v_succ_x3f_1973_);
                    lean_dec_ref(v_inst_1972_);
                    return v_acc_1975_;
                } else {
                    v_upperBound_1978_ = lean_ctor_get(v_it_1974_, 1);
                    v_isSharedCheck_1991_ = (!lean_is_exclusive(v_it_1974_)) as u8;
                    if v_isSharedCheck_1991_ == 0 {
                        v_unused_1992_ = lean_ctor_get(v_it_1974_, 0);
                        lean_dec(v_unused_1992_);
                        v___x_1980_ = v_it_1974_;
                        v_isShared_1981_ = v_isSharedCheck_1991_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_upperBound_1978_);
                        lean_dec(v_it_1974_);
                        v___x_1980_ = lean_box(0);
                        v_isShared_1981_ = v_isSharedCheck_1991_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1982_ = lean_ctor_get(v_next_1977_, 0);
                lean_inc_n(v_val_1982_, 2);
                lean_dec_ref_known(v_next_1977_, 1);
                lean_inc(v_upperBound_1978_);
                v___x_1983_ = lean_apply_2(v_inst_1972_, v_val_1982_, v_upperBound_1978_);
                v___x_1984_ = (lean_unbox(v___x_1983_) as u8);
                if v___x_1984_ == 0 {
                    lean_dec(v_val_1982_);
                    lean_del_object(v___x_1980_);
                    lean_dec(v_upperBound_1978_);
                    lean_dec_ref(v_recur_1976_);
                    lean_dec_ref(v_succ_x3f_1973_);
                    return v_acc_1975_;
                } else {
                    lean_inc(v_val_1982_);
                    v___x_1985_ = lean_apply_1(v_succ_x3f_1973_, v_val_1982_);
                    if v_isShared_1981_ == 0 {
                        lean_ctor_set(v___x_1980_, 0, v___x_1985_);
                        v___x_1987_ = v___x_1980_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1985_);
                        lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_upperBound_1978_);
                        v___x_1987_ = v_reuseFailAlloc_1990_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1988_ = lean_array_push(v_acc_1975_, v_val_1982_);
                v___x_1989_ = lean_apply_3(v_recur_1976_, v___x_1987_, v___x_1988_, lean_box(0));
                return v___x_1989_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roo_toList___redArg(
    mut v_inst_1993_: *mut LeanObject,
    mut v_inst_1994_: *mut LeanObject,
    mut v_r_1995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2001_: u8 = 0;
    let mut v___f_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_1996_ = lean_ctor_get(v_inst_1994_, 0);
                lean_inc_ref(v_succ_x3f_1996_);
                lean_dec_ref(v_inst_1994_);
                v_lower_1997_ = lean_ctor_get(v_r_1995_, 0);
                v_upper_1998_ = lean_ctor_get(v_r_1995_, 1);
                v_isSharedCheck_2010_ = (!lean_is_exclusive(v_r_1995_)) as u8;
                if v_isSharedCheck_2010_ == 0 {
                    v___x_2000_ = v_r_1995_;
                    v_isShared_2001_ = v_isSharedCheck_2010_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_1998_);
                    lean_inc(v_lower_1997_);
                    lean_dec(v_r_1995_);
                    v___x_2000_ = lean_box(0);
                    v_isShared_2001_ = v_isSharedCheck_2010_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_succ_x3f_1996_);
                v___f_2002_ = lean_alloc_closure(
                    l_Std_Roo_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_2002_, 0, v_inst_1993_);
                lean_closure_set(v___f_2002_, 1, v_succ_x3f_1996_);
                v___x_2003_ = lean_apply_1(v_succ_x3f_1996_, v_lower_1997_);
                if v_isShared_2001_ == 0 {
                    lean_ctor_set(v___x_2000_, 0, v___x_2003_);
                    v___x_2005_ = v___x_2000_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2003_);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_upper_1998_);
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
    mut v_00_u03b1_2011_: *mut LeanObject,
    mut v_inst_2012_: *mut LeanObject,
    mut v_inst_2013_: *mut LeanObject,
    mut v_inst_2014_: *mut LeanObject,
    mut v_inst_2015_: *mut LeanObject,
    mut v_inst_2016_: *mut LeanObject,
    mut v_r_2017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2023_: u8 = 0;
    let mut v___f_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_2018_ = lean_ctor_get(v_inst_2014_, 0);
                lean_inc_ref(v_succ_x3f_2018_);
                lean_dec_ref(v_inst_2014_);
                v_lower_2019_ = lean_ctor_get(v_r_2017_, 0);
                v_upper_2020_ = lean_ctor_get(v_r_2017_, 1);
                v_isSharedCheck_2032_ = (!lean_is_exclusive(v_r_2017_)) as u8;
                if v_isSharedCheck_2032_ == 0 {
                    v___x_2022_ = v_r_2017_;
                    v_isShared_2023_ = v_isSharedCheck_2032_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_2020_);
                    lean_inc(v_lower_2019_);
                    lean_dec(v_r_2017_);
                    v___x_2022_ = lean_box(0);
                    v_isShared_2023_ = v_isSharedCheck_2032_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_succ_x3f_2018_);
                v___f_2024_ = lean_alloc_closure(
                    l_Std_Roo_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_2024_, 0, v_inst_2013_);
                lean_closure_set(v___f_2024_, 1, v_succ_x3f_2018_);
                v___x_2025_ = lean_apply_1(v_succ_x3f_2018_, v_lower_2019_);
                if v_isShared_2023_ == 0 {
                    lean_ctor_set(v___x_2022_, 0, v___x_2025_);
                    v___x_2027_ = v___x_2022_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2025_);
                    lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_upper_2020_);
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
    mut v_inst_2033_: *mut LeanObject,
    mut v_inst_2034_: *mut LeanObject,
    mut v_r_2035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2041_: u8 = 0;
    let mut v___f_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_2036_ = lean_ctor_get(v_inst_2034_, 0);
                lean_inc_ref(v_succ_x3f_2036_);
                lean_dec_ref(v_inst_2034_);
                v_lower_2037_ = lean_ctor_get(v_r_2035_, 0);
                v_upper_2038_ = lean_ctor_get(v_r_2035_, 1);
                v_isSharedCheck_2049_ = (!lean_is_exclusive(v_r_2035_)) as u8;
                if v_isSharedCheck_2049_ == 0 {
                    v___x_2040_ = v_r_2035_;
                    v_isShared_2041_ = v_isSharedCheck_2049_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_2038_);
                    lean_inc(v_lower_2037_);
                    lean_dec(v_r_2035_);
                    v___x_2040_ = lean_box(0);
                    v_isShared_2041_ = v_isSharedCheck_2049_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_succ_x3f_2036_);
                v___f_2042_ = lean_alloc_closure(
                    l_Std_Roo_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_2042_, 0, v_inst_2033_);
                lean_closure_set(v___f_2042_, 1, v_succ_x3f_2036_);
                v___x_2043_ = lean_apply_1(v_succ_x3f_2036_, v_lower_2037_);
                if v_isShared_2041_ == 0 {
                    lean_ctor_set(v___x_2040_, 0, v___x_2043_);
                    v___x_2045_ = v___x_2040_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2043_);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_upper_2038_);
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
    mut v_00_u03b1_2050_: *mut LeanObject,
    mut v_inst_2051_: *mut LeanObject,
    mut v_inst_2052_: *mut LeanObject,
    mut v_inst_2053_: *mut LeanObject,
    mut v_inst_2054_: *mut LeanObject,
    mut v_inst_2055_: *mut LeanObject,
    mut v_r_2056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___f_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2070_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_2057_ = lean_ctor_get(v_inst_2053_, 0);
                lean_inc_ref(v_succ_x3f_2057_);
                lean_dec_ref(v_inst_2053_);
                v_lower_2058_ = lean_ctor_get(v_r_2056_, 0);
                v_upper_2059_ = lean_ctor_get(v_r_2056_, 1);
                v_isSharedCheck_2070_ = (!lean_is_exclusive(v_r_2056_)) as u8;
                if v_isSharedCheck_2070_ == 0 {
                    v___x_2061_ = v_r_2056_;
                    v_isShared_2062_ = v_isSharedCheck_2070_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_2059_);
                    lean_inc(v_lower_2058_);
                    lean_dec(v_r_2056_);
                    v___x_2061_ = lean_box(0);
                    v_isShared_2062_ = v_isSharedCheck_2070_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_succ_x3f_2057_);
                v___f_2063_ = lean_alloc_closure(
                    l_Std_Roo_toList___redArg___lam__0 as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_2063_, 0, v_inst_2052_);
                lean_closure_set(v___f_2063_, 1, v_succ_x3f_2057_);
                v___x_2064_ = lean_apply_1(v_succ_x3f_2057_, v_lower_2058_);
                if v_isShared_2062_ == 0 {
                    lean_ctor_set(v___x_2061_, 0, v___x_2064_);
                    v___x_2066_ = v___x_2061_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2064_);
                    lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_upper_2059_);
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
    mut v_inst_2071_: *mut LeanObject,
    mut v_inst_2072_: *mut LeanObject,
    mut v_r_2073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_2074_ = lean_ctor_get(v_inst_2072_, 0);
    lean_inc_ref(v_succ_x3f_2074_);
    lean_dec_ref(v_inst_2072_);
    v_lower_2075_ = lean_ctor_get(v_r_2073_, 0);
    lean_inc(v_lower_2075_);
    v_upper_2076_ = lean_ctor_get(v_r_2073_, 1);
    lean_inc(v_upper_2076_);
    lean_dec_ref(v_r_2073_);
    v___x_2077_ = lean_apply_1(v_succ_x3f_2074_, v_lower_2075_);
    if lean_obj_tag(v___x_2077_) == 0 {
        let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_upper_2076_);
        lean_dec_ref(v_inst_2071_);
        v___x_2078_ = lean_unsigned_to_nat(0);
        return v___x_2078_;
    } else {
        let mut v_val_2079_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
        v_val_2079_ = lean_ctor_get(v___x_2077_, 0);
        lean_inc(v_val_2079_);
        lean_dec_ref_known(v___x_2077_, 1);
        v___x_2080_ = lean_apply_2(v_inst_2071_, v_val_2079_, v_upper_2076_);
        return v___x_2080_;
    }
}
pub unsafe fn l_Std_Roo_size(
    mut v_00_u03b1_2081_: *mut LeanObject,
    mut v_inst_2082_: *mut LeanObject,
    mut v_inst_2083_: *mut LeanObject,
    mut v_r_2084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_2085_ = lean_ctor_get(v_inst_2083_, 0);
    lean_inc_ref(v_succ_x3f_2085_);
    lean_dec_ref(v_inst_2083_);
    v_lower_2086_ = lean_ctor_get(v_r_2084_, 0);
    lean_inc(v_lower_2086_);
    v_upper_2087_ = lean_ctor_get(v_r_2084_, 1);
    lean_inc(v_upper_2087_);
    lean_dec_ref(v_r_2084_);
    v___x_2088_ = lean_apply_1(v_succ_x3f_2085_, v_lower_2086_);
    if lean_obj_tag(v___x_2088_) == 0 {
        let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_upper_2087_);
        lean_dec_ref(v_inst_2082_);
        v___x_2089_ = lean_unsigned_to_nat(0);
        return v___x_2089_;
    } else {
        let mut v_val_2090_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
        v_val_2090_ = lean_ctor_get(v___x_2088_, 0);
        lean_inc(v_val_2090_);
        lean_dec_ref_known(v___x_2088_, 1);
        v___x_2091_ = lean_apply_2(v_inst_2082_, v_val_2090_, v_upper_2087_);
        return v___x_2091_;
    }
}
pub unsafe fn l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3(
    mut v_inst_2092_: *mut LeanObject,
    mut v_inst_2093_: *mut LeanObject,
    mut v_inst_2094_: *mut LeanObject,
    mut v_00_u03b2_2095_: *mut LeanObject,
    mut v_r_2096_: *mut LeanObject,
    mut v_init_2097_: *mut LeanObject,
    mut v_f_2098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2099_ = lean_ctor_get(v_inst_2093_, 0);
    lean_inc_ref(v_toApplicative_2099_);
    v_succ_x3f_2100_ = lean_ctor_get(v_inst_2092_, 0);
    lean_inc_ref_n(v_succ_x3f_2100_, 2);
    lean_dec_ref(v_inst_2092_);
    v_lower_2101_ = lean_ctor_get(v_r_2096_, 0);
    lean_inc(v_lower_2101_);
    v_upper_2102_ = lean_ctor_get(v_r_2096_, 1);
    lean_inc(v_upper_2102_);
    lean_dec_ref(v_r_2096_);
    v_toBind_2103_ = lean_ctor_get(v_inst_2093_, 1);
    lean_inc(v_toBind_2103_);
    lean_dec_ref(v_inst_2093_);
    v_toPure_2104_ = lean_ctor_get(v_toApplicative_2099_, 1);
    lean_inc(v_toPure_2104_);
    lean_dec_ref(v_toApplicative_2099_);
    v___x_2105_ = lean_apply_1(v_succ_x3f_2100_, v_lower_2101_);
    if lean_obj_tag(v___x_2105_) == 0 {
        let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_2103_);
        lean_dec(v_upper_2102_);
        lean_dec_ref(v_succ_x3f_2100_);
        lean_dec(v_f_2098_);
        lean_dec_ref(v_inst_2094_);
        v___x_2106_ = lean_apply_2(v_toPure_2104_, lean_box(0), v_init_2097_);
        return v___x_2106_;
    } else {
        let mut v_val_2107_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2108_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2109_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
        v_val_2107_ = lean_ctor_get(v___x_2105_, 0);
        lean_inc(v_val_2107_);
        lean_dec_ref_known(v___x_2105_, 1);
        lean_inc(v_toPure_2104_);
        v___f_2108_ = lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
        lean_closure_set(v___f_2108_, 0, v_toPure_2104_);
        v___f_2109_ = lean_alloc_closure(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 11, 7);
        lean_closure_set(v___f_2109_, 0, v_inst_2094_);
        lean_closure_set(v___f_2109_, 1, v_upper_2102_);
        lean_closure_set(v___f_2109_, 2, v_toPure_2104_);
        lean_closure_set(v___f_2109_, 3, v_succ_x3f_2100_);
        lean_closure_set(v___f_2109_, 4, v_f_2098_);
        lean_closure_set(v___f_2109_, 5, v_toBind_2103_);
        lean_closure_set(v___f_2109_, 6, v___f_2108_);
        v___x_2110_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_2109_,
            v_val_2107_,
            v_init_2097_,
            lean_box(0),
        );
        return v___x_2110_;
    }
}
pub unsafe fn l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_2111_: *mut LeanObject,
    mut v_inst_2112_: *mut LeanObject,
    mut v_inst_2113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2114_: *mut LeanObject = core::ptr::null_mut();
    v___f_2114_ = lean_alloc_closure(l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3 as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___f_2114_, 0, v_inst_2111_);
    lean_closure_set(v___f_2114_, 1, v_inst_2113_);
    lean_closure_set(v___f_2114_, 2, v_inst_2112_);
    return v___f_2114_;
}
pub unsafe fn l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_2115_: *mut LeanObject,
    mut v_m_2116_: *mut LeanObject,
    mut v_inst_2117_: *mut LeanObject,
    mut v_inst_2118_: *mut LeanObject,
    mut v_inst_2119_: *mut LeanObject,
    mut v_inst_2120_: *mut LeanObject,
    mut v_inst_2121_: *mut LeanObject,
    mut v_inst_2122_: *mut LeanObject,
    mut v_inst_2123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2124_: *mut LeanObject = core::ptr::null_mut();
    v___f_2124_ = lean_alloc_closure(l_Std_Roo_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__3 as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___f_2124_, 0, v_inst_2117_);
    lean_closure_set(v___f_2124_, 1, v_inst_2122_);
    lean_closure_set(v___f_2124_, 2, v_inst_2119_);
    return v___f_2124_;
}
pub unsafe fn l_Std_Roi_Internal_iter___redArg(
    mut v_inst_2125_: *mut LeanObject,
    mut v_r_2126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_2127_ = lean_ctor_get(v_inst_2125_, 0);
    lean_inc_ref(v_succ_x3f_2127_);
    lean_dec_ref(v_inst_2125_);
    v___x_2128_ = lean_apply_1(v_succ_x3f_2127_, v_r_2126_);
    return v___x_2128_;
}
pub unsafe fn l_Std_Roi_Internal_iter(
    mut v_00_u03b1_2129_: *mut LeanObject,
    mut v_inst_2130_: *mut LeanObject,
    mut v_r_2131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_2132_ = lean_ctor_get(v_inst_2130_, 0);
    lean_inc_ref(v_succ_x3f_2132_);
    lean_dec_ref(v_inst_2130_);
    v___x_2133_ = lean_apply_1(v_succ_x3f_2132_, v_r_2131_);
    return v___x_2133_;
}
pub unsafe fn l_Std_Roi_toList___redArg___lam__0(
    mut v_succ_x3f_2134_: *mut LeanObject,
    mut v_it_2135_: *mut LeanObject,
    mut v_acc_2136_: *mut LeanObject,
    mut v_recur_2137_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_2135_) == 0 {
        lean_dec_ref(v_recur_2137_);
        lean_dec_ref(v_succ_x3f_2134_);
        return v_acc_2136_;
    } else {
        let mut v_val_2138_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
        v_val_2138_ = lean_ctor_get(v_it_2135_, 0);
        lean_inc_n(v_val_2138_, 2);
        lean_dec_ref_known(v_it_2135_, 1);
        v___x_2139_ = lean_apply_1(v_succ_x3f_2134_, v_val_2138_);
        v___x_2140_ = lean_array_push(v_acc_2136_, v_val_2138_);
        v___x_2141_ = lean_apply_3(v_recur_2137_, v___x_2139_, v___x_2140_, lean_box(0));
        return v___x_2141_;
    }
}
pub unsafe fn l_Std_Roi_toList___redArg(
    mut v_inst_2142_: *mut LeanObject,
    mut v_r_2143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_2144_ = lean_ctor_get(v_inst_2142_, 0);
    lean_inc_ref_n(v_succ_x3f_2144_, 2);
    lean_dec_ref(v_inst_2142_);
    v___f_2145_ = lean_alloc_closure(
        l_Std_Roi_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2145_, 0, v_succ_x3f_2144_);
    v___x_2146_ = lean_apply_1(v_succ_x3f_2144_, v_r_2143_);
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
    mut v_00_u03b1_2150_: *mut LeanObject,
    mut v_inst_2151_: *mut LeanObject,
    mut v_inst_2152_: *mut LeanObject,
    mut v_inst_2153_: *mut LeanObject,
    mut v_r_2154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_2155_ = lean_ctor_get(v_inst_2151_, 0);
    lean_inc_ref_n(v_succ_x3f_2155_, 2);
    lean_dec_ref(v_inst_2151_);
    v___f_2156_ = lean_alloc_closure(
        l_Std_Roi_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2156_, 0, v_succ_x3f_2155_);
    v___x_2157_ = lean_apply_1(v_succ_x3f_2155_, v_r_2154_);
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
    mut v_inst_2161_: *mut LeanObject,
    mut v_r_2162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_2163_ = lean_ctor_get(v_inst_2161_, 0);
    lean_inc_ref_n(v_succ_x3f_2163_, 2);
    lean_dec_ref(v_inst_2161_);
    v___f_2164_ = lean_alloc_closure(
        l_Std_Roi_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2164_, 0, v_succ_x3f_2163_);
    v___x_2165_ = lean_apply_1(v_succ_x3f_2163_, v_r_2162_);
    v___x_2166_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2167_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2164_,
        v___x_2165_,
        v___x_2166_,
    );
    return v___x_2167_;
}
pub unsafe fn l_Std_Roi_toArray(
    mut v_00_u03b1_2168_: *mut LeanObject,
    mut v_inst_2169_: *mut LeanObject,
    mut v_inst_2170_: *mut LeanObject,
    mut v_inst_2171_: *mut LeanObject,
    mut v_r_2172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_2173_ = lean_ctor_get(v_inst_2169_, 0);
    lean_inc_ref_n(v_succ_x3f_2173_, 2);
    lean_dec_ref(v_inst_2169_);
    v___f_2174_ = lean_alloc_closure(
        l_Std_Roi_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2174_, 0, v_succ_x3f_2173_);
    v___x_2175_ = lean_apply_1(v_succ_x3f_2173_, v_r_2172_);
    v___x_2176_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2177_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2174_,
        v___x_2175_,
        v___x_2176_,
    );
    return v___x_2177_;
}
pub unsafe fn l_Std_Roi_size___redArg(
    mut v_inst_2178_: *mut LeanObject,
    mut v_inst_2179_: *mut LeanObject,
    mut v_r_2180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_2181_ = lean_ctor_get(v_inst_2179_, 0);
    lean_inc_ref(v_succ_x3f_2181_);
    lean_dec_ref(v_inst_2179_);
    v___x_2182_ = lean_apply_1(v_succ_x3f_2181_, v_r_2180_);
    if lean_obj_tag(v___x_2182_) == 0 {
        let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_2178_);
        v___x_2183_ = lean_unsigned_to_nat(0);
        return v___x_2183_;
    } else {
        let mut v_val_2184_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
        v_val_2184_ = lean_ctor_get(v___x_2182_, 0);
        lean_inc(v_val_2184_);
        lean_dec_ref_known(v___x_2182_, 1);
        v___x_2185_ = lean_apply_1(v_inst_2178_, v_val_2184_);
        return v___x_2185_;
    }
}
pub unsafe fn l_Std_Roi_size(
    mut v_00_u03b1_2186_: *mut LeanObject,
    mut v_inst_2187_: *mut LeanObject,
    mut v_inst_2188_: *mut LeanObject,
    mut v_r_2189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_2190_ = lean_ctor_get(v_inst_2188_, 0);
    lean_inc_ref(v_succ_x3f_2190_);
    lean_dec_ref(v_inst_2188_);
    v___x_2191_ = lean_apply_1(v_succ_x3f_2190_, v_r_2189_);
    if lean_obj_tag(v___x_2191_) == 0 {
        let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_2187_);
        v___x_2192_ = lean_unsigned_to_nat(0);
        return v___x_2192_;
    } else {
        let mut v_val_2193_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
        v_val_2193_ = lean_ctor_get(v___x_2191_, 0);
        lean_inc(v_val_2193_);
        lean_dec_ref_known(v___x_2191_, 1);
        v___x_2194_ = lean_apply_1(v_inst_2187_, v_val_2193_);
        return v___x_2194_;
    }
}
pub unsafe fn l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2(
    mut v_toPure_2195_: *mut LeanObject,
    mut v_succ_x3f_2196_: *mut LeanObject,
    mut v_f_2197_: *mut LeanObject,
    mut v_toBind_2198_: *mut LeanObject,
    mut v___f_2199_: *mut LeanObject,
    mut v_next_2200_: *mut LeanObject,
    mut v_acc_2201_: *mut LeanObject,
    mut v_h_2202_: *mut LeanObject,
    mut v_G_2203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_next_2200_);
    v___f_2204_ = lean_alloc_closure(l_Std_Roc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__1 as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___f_2204_, 0, v_toPure_2195_);
    lean_closure_set(v___f_2204_, 1, v_succ_x3f_2196_);
    lean_closure_set(v___f_2204_, 2, v_next_2200_);
    lean_closure_set(v___f_2204_, 3, v_G_2203_);
    v___x_2205_ = lean_apply_3(v_f_2197_, v_next_2200_, lean_box(0), v_acc_2201_);
    lean_inc(v_toBind_2198_);
    v___x_2206_ = lean_apply_4(
        v_toBind_2198_,
        lean_box(0),
        lean_box(0),
        v___x_2205_,
        v___f_2199_,
    );
    v___x_2207_ = lean_apply_4(
        v_toBind_2198_,
        lean_box(0),
        lean_box(0),
        v___x_2206_,
        v___f_2204_,
    );
    return v___x_2207_;
}
pub unsafe fn l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0(
    mut v_inst_2208_: *mut LeanObject,
    mut v_inst_2209_: *mut LeanObject,
    mut v_00_u03b2_2210_: *mut LeanObject,
    mut v_r_2211_: *mut LeanObject,
    mut v_init_2212_: *mut LeanObject,
    mut v_f_2213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_next_2218_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2214_ = lean_ctor_get(v_inst_2209_, 0);
    lean_inc_ref(v_toApplicative_2214_);
    v_succ_x3f_2215_ = lean_ctor_get(v_inst_2208_, 0);
    lean_inc_ref_n(v_succ_x3f_2215_, 2);
    lean_dec_ref(v_inst_2208_);
    v_toBind_2216_ = lean_ctor_get(v_inst_2209_, 1);
    lean_inc(v_toBind_2216_);
    lean_dec_ref(v_inst_2209_);
    v_toPure_2217_ = lean_ctor_get(v_toApplicative_2214_, 1);
    lean_inc(v_toPure_2217_);
    lean_dec_ref(v_toApplicative_2214_);
    v_next_2218_ = lean_apply_1(v_succ_x3f_2215_, v_r_2211_);
    if lean_obj_tag(v_next_2218_) == 0 {
        let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_2216_);
        lean_dec_ref(v_succ_x3f_2215_);
        lean_dec(v_f_2213_);
        v___x_2219_ = lean_apply_2(v_toPure_2217_, lean_box(0), v_init_2212_);
        return v___x_2219_;
    } else {
        let mut v_val_2220_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2221_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2222_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
        v_val_2220_ = lean_ctor_get(v_next_2218_, 0);
        lean_inc(v_val_2220_);
        lean_dec_ref_known(v_next_2218_, 1);
        lean_inc(v_toPure_2217_);
        v___f_2221_ = lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
        lean_closure_set(v___f_2221_, 0, v_toPure_2217_);
        v___f_2222_ = lean_alloc_closure(l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__2 as *mut core::ffi::c_void, 9, 5);
        lean_closure_set(v___f_2222_, 0, v_toPure_2217_);
        lean_closure_set(v___f_2222_, 1, v_succ_x3f_2215_);
        lean_closure_set(v___f_2222_, 2, v_f_2213_);
        lean_closure_set(v___f_2222_, 3, v_toBind_2216_);
        lean_closure_set(v___f_2222_, 4, v___f_2221_);
        v___x_2223_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_2222_,
            v_val_2220_,
            v_init_2212_,
            lean_box(0),
        );
        return v___x_2223_;
    }
}
pub unsafe fn l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_2224_: *mut LeanObject,
    mut v_inst_2225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2226_: *mut LeanObject = core::ptr::null_mut();
    v___f_2226_ = lean_alloc_closure(l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 6, 2);
    lean_closure_set(v___f_2226_, 0, v_inst_2224_);
    lean_closure_set(v___f_2226_, 1, v_inst_2225_);
    return v___f_2226_;
}
pub unsafe fn l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_2227_: *mut LeanObject,
    mut v_m_2228_: *mut LeanObject,
    mut v_inst_2229_: *mut LeanObject,
    mut v_inst_2230_: *mut LeanObject,
    mut v_inst_2231_: *mut LeanObject,
    mut v_inst_2232_: *mut LeanObject,
    mut v_inst_2233_: *mut LeanObject,
    mut v_inst_2234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2235_: *mut LeanObject = core::ptr::null_mut();
    v___f_2235_ = lean_alloc_closure(l_Std_Roi_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 6, 2);
    lean_closure_set(v___f_2235_, 0, v_inst_2229_);
    lean_closure_set(v___f_2235_, 1, v_inst_2233_);
    return v___f_2235_;
}
pub unsafe fn l_Std_Ric_Internal_iter___redArg(
    mut v_inst_2236_: *mut LeanObject,
    mut v_r_2237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    v___x_2238_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2238_, 0, v_inst_2236_);
    lean_ctor_set(v___x_2238_, 1, v_r_2237_);
    return v___x_2238_;
}
pub unsafe fn l_Std_Ric_Internal_iter(
    mut v_00_u03b1_2239_: *mut LeanObject,
    mut v_inst_2240_: *mut LeanObject,
    mut v_r_2241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    v___x_2242_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2242_, 0, v_inst_2240_);
    lean_ctor_set(v___x_2242_, 1, v_r_2241_);
    return v___x_2242_;
}
pub unsafe fn l_Std_Ric_toList___redArg(
    mut v_inst_2243_: *mut LeanObject,
    mut v_inst_2244_: *mut LeanObject,
    mut v_inst_2245_: *mut LeanObject,
    mut v_r_2246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    v___f_2247_ = lean_alloc_closure(
        l_Std_Rcc_toList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2247_, 0, v_inst_2244_);
    lean_closure_set(v___f_2247_, 1, v_inst_2245_);
    v___x_2248_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2248_, 0, v_inst_2243_);
    lean_ctor_set(v___x_2248_, 1, v_r_2246_);
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
    mut v_00_u03b1_2252_: *mut LeanObject,
    mut v_inst_2253_: *mut LeanObject,
    mut v_inst_2254_: *mut LeanObject,
    mut v_inst_2255_: *mut LeanObject,
    mut v_inst_2256_: *mut LeanObject,
    mut v_inst_2257_: *mut LeanObject,
    mut v_inst_2258_: *mut LeanObject,
    mut v_r_2259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    v___f_2260_ = lean_alloc_closure(
        l_Std_Rcc_toList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2260_, 0, v_inst_2255_);
    lean_closure_set(v___f_2260_, 1, v_inst_2256_);
    v___x_2261_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2261_, 0, v_inst_2253_);
    lean_ctor_set(v___x_2261_, 1, v_r_2259_);
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
    mut v_inst_2265_: *mut LeanObject,
    mut v_inst_2266_: *mut LeanObject,
    mut v_inst_2267_: *mut LeanObject,
    mut v_r_2268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    v___f_2269_ = lean_alloc_closure(
        l_Std_Rcc_toList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2269_, 0, v_inst_2266_);
    lean_closure_set(v___f_2269_, 1, v_inst_2267_);
    v___x_2270_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2270_, 0, v_inst_2265_);
    lean_ctor_set(v___x_2270_, 1, v_r_2268_);
    v___x_2271_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2272_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2269_,
        v___x_2270_,
        v___x_2271_,
    );
    return v___x_2272_;
}
pub unsafe fn l_Std_Ric_toArray(
    mut v_00_u03b1_2273_: *mut LeanObject,
    mut v_inst_2274_: *mut LeanObject,
    mut v_inst_2275_: *mut LeanObject,
    mut v_inst_2276_: *mut LeanObject,
    mut v_inst_2277_: *mut LeanObject,
    mut v_inst_2278_: *mut LeanObject,
    mut v_inst_2279_: *mut LeanObject,
    mut v_r_2280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    v___f_2281_ = lean_alloc_closure(
        l_Std_Rcc_toList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2281_, 0, v_inst_2276_);
    lean_closure_set(v___f_2281_, 1, v_inst_2277_);
    v___x_2282_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2282_, 0, v_inst_2274_);
    lean_ctor_set(v___x_2282_, 1, v_r_2280_);
    v___x_2283_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2284_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2281_,
        v___x_2282_,
        v___x_2283_,
    );
    return v___x_2284_;
}
pub unsafe fn l_Std_Ric_size___redArg(
    mut v_inst_2285_: *mut LeanObject,
    mut v_inst_2286_: *mut LeanObject,
    mut v_r_2287_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_inst_2286_) == 0 {
        let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_r_2287_);
        lean_dec_ref(v_inst_2285_);
        v___x_2288_ = lean_unsigned_to_nat(0);
        return v___x_2288_;
    } else {
        let mut v_val_2289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
        v_val_2289_ = lean_ctor_get(v_inst_2286_, 0);
        lean_inc(v_val_2289_);
        lean_dec_ref_known(v_inst_2286_, 1);
        v___x_2290_ = lean_apply_2(v_inst_2285_, v_val_2289_, v_r_2287_);
        return v___x_2290_;
    }
}
pub unsafe fn l_Std_Ric_size(
    mut v_00_u03b1_2291_: *mut LeanObject,
    mut v_inst_2292_: *mut LeanObject,
    mut v_inst_2293_: *mut LeanObject,
    mut v_r_2294_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_inst_2293_) == 0 {
        let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_r_2294_);
        lean_dec_ref(v_inst_2292_);
        v___x_2295_ = lean_unsigned_to_nat(0);
        return v___x_2295_;
    } else {
        let mut v_val_2296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
        v_val_2296_ = lean_ctor_get(v_inst_2293_, 0);
        lean_inc(v_val_2296_);
        lean_dec_ref_known(v_inst_2293_, 1);
        v___x_2297_ = lean_apply_2(v_inst_2292_, v_val_2296_, v_r_2294_);
        return v___x_2297_;
    }
}
pub unsafe fn l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__2(
    mut v_inst_2298_: *mut LeanObject,
    mut v_r_2299_: *mut LeanObject,
    mut v_toPure_2300_: *mut LeanObject,
    mut v_inst_2301_: *mut LeanObject,
    mut v_f_2302_: *mut LeanObject,
    mut v_toBind_2303_: *mut LeanObject,
    mut v___f_2304_: *mut LeanObject,
    mut v_next_2305_: *mut LeanObject,
    mut v_acc_2306_: *mut LeanObject,
    mut v_h_2307_: *mut LeanObject,
    mut v_G_2308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    lean_inc(v_next_2305_);
    v___x_2309_ = lean_apply_2(v_inst_2298_, v_next_2305_, v_r_2299_);
    v___x_2310_ = (lean_unbox(v___x_2309_) as u8);
    if v___x_2310_ == 0 {
        let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_G_2308_);
        lean_dec(v_next_2305_);
        lean_dec(v___f_2304_);
        lean_dec(v_toBind_2303_);
        lean_dec(v_f_2302_);
        lean_dec_ref(v_inst_2301_);
        v___x_2311_ = lean_apply_2(v_toPure_2300_, lean_box(0), v_acc_2306_);
        return v___x_2311_;
    } else {
        let mut v___f_2312_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_next_2305_);
        v___f_2312_ = lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__1 as *mut core::ffi::c_void, 5, 4);
        lean_closure_set(v___f_2312_, 0, v_toPure_2300_);
        lean_closure_set(v___f_2312_, 1, v_inst_2301_);
        lean_closure_set(v___f_2312_, 2, v_next_2305_);
        lean_closure_set(v___f_2312_, 3, v_G_2308_);
        v___x_2313_ = lean_apply_3(v_f_2302_, v_next_2305_, lean_box(0), v_acc_2306_);
        lean_inc(v_toBind_2303_);
        v___x_2314_ = lean_apply_4(
            v_toBind_2303_,
            lean_box(0),
            lean_box(0),
            v___x_2313_,
            v___f_2304_,
        );
        v___x_2315_ = lean_apply_4(
            v_toBind_2303_,
            lean_box(0),
            lean_box(0),
            v___x_2314_,
            v___f_2312_,
        );
        return v___x_2315_;
    }
}
pub unsafe fn l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__0(
    mut v_inst_2316_: *mut LeanObject,
    mut v_inst_2317_: *mut LeanObject,
    mut v_inst_2318_: *mut LeanObject,
    mut v_inst_2319_: *mut LeanObject,
    mut v_00_u03b2_2320_: *mut LeanObject,
    mut v_r_2321_: *mut LeanObject,
    mut v_init_2322_: *mut LeanObject,
    mut v_f_2323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2324_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2324_ = lean_ctor_get(v_inst_2316_, 0);
    lean_inc_ref(v_toApplicative_2324_);
    if lean_obj_tag(v_inst_2317_) == 0 {
        let mut v_toPure_2325_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_2323_);
        lean_dec(v_r_2321_);
        lean_dec_ref(v_inst_2319_);
        lean_dec_ref(v_inst_2318_);
        lean_dec_ref(v_inst_2316_);
        v_toPure_2325_ = lean_ctor_get(v_toApplicative_2324_, 1);
        lean_inc(v_toPure_2325_);
        lean_dec_ref(v_toApplicative_2324_);
        v___x_2326_ = lean_apply_2(v_toPure_2325_, lean_box(0), v_init_2322_);
        return v___x_2326_;
    } else {
        let mut v_toBind_2327_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_2328_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_2329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2330_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2331_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_2327_ = lean_ctor_get(v_inst_2316_, 1);
        lean_inc(v_toBind_2327_);
        lean_dec_ref(v_inst_2316_);
        v_toPure_2328_ = lean_ctor_get(v_toApplicative_2324_, 1);
        lean_inc_n(v_toPure_2328_, 2);
        lean_dec_ref(v_toApplicative_2324_);
        v_val_2329_ = lean_ctor_get(v_inst_2317_, 0);
        lean_inc(v_val_2329_);
        lean_dec_ref_known(v_inst_2317_, 1);
        v___f_2330_ = lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
        lean_closure_set(v___f_2330_, 0, v_toPure_2328_);
        v___f_2331_ = lean_alloc_closure(l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__2 as *mut core::ffi::c_void, 11, 7);
        lean_closure_set(v___f_2331_, 0, v_inst_2318_);
        lean_closure_set(v___f_2331_, 1, v_r_2321_);
        lean_closure_set(v___f_2331_, 2, v_toPure_2328_);
        lean_closure_set(v___f_2331_, 3, v_inst_2319_);
        lean_closure_set(v___f_2331_, 4, v_f_2323_);
        lean_closure_set(v___f_2331_, 5, v_toBind_2327_);
        lean_closure_set(v___f_2331_, 6, v___f_2330_);
        v___x_2332_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_2331_,
            v_val_2329_,
            v_init_2322_,
            lean_box(0),
        );
        return v___x_2332_;
    }
}
pub unsafe fn l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_2333_: *mut LeanObject,
    mut v_inst_2334_: *mut LeanObject,
    mut v_inst_2335_: *mut LeanObject,
    mut v_inst_2336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2337_: *mut LeanObject = core::ptr::null_mut();
    v___f_2337_ = lean_alloc_closure(l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 8, 4);
    lean_closure_set(v___f_2337_, 0, v_inst_2336_);
    lean_closure_set(v___f_2337_, 1, v_inst_2335_);
    lean_closure_set(v___f_2337_, 2, v_inst_2334_);
    lean_closure_set(v___f_2337_, 3, v_inst_2333_);
    return v___f_2337_;
}
pub unsafe fn l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_2338_: *mut LeanObject,
    mut v_m_2339_: *mut LeanObject,
    mut v_inst_2340_: *mut LeanObject,
    mut v_inst_2341_: *mut LeanObject,
    mut v_inst_2342_: *mut LeanObject,
    mut v_inst_2343_: *mut LeanObject,
    mut v_inst_2344_: *mut LeanObject,
    mut v_inst_2345_: *mut LeanObject,
    mut v_inst_2346_: *mut LeanObject,
    mut v_inst_2347_: *mut LeanObject,
    mut v_inst_2348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2349_: *mut LeanObject = core::ptr::null_mut();
    v___f_2349_ = lean_alloc_closure(l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 8, 4);
    lean_closure_set(v___f_2349_, 0, v_inst_2347_);
    lean_closure_set(v___f_2349_, 1, v_inst_2343_);
    lean_closure_set(v___f_2349_, 2, v_inst_2342_);
    lean_closure_set(v___f_2349_, 3, v_inst_2340_);
    return v___f_2349_;
}
pub unsafe fn l_Std_Rio_Internal_iter___redArg(
    mut v_inst_2350_: *mut LeanObject,
    mut v_r_2351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    v___x_2352_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2352_, 0, v_inst_2350_);
    lean_ctor_set(v___x_2352_, 1, v_r_2351_);
    return v___x_2352_;
}
pub unsafe fn l_Std_Rio_Internal_iter(
    mut v_00_u03b1_2353_: *mut LeanObject,
    mut v_inst_2354_: *mut LeanObject,
    mut v_inst_2355_: *mut LeanObject,
    mut v_r_2356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    v___x_2357_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2357_, 0, v_inst_2355_);
    lean_ctor_set(v___x_2357_, 1, v_r_2356_);
    return v___x_2357_;
}
pub unsafe fn l_Std_Rio_Internal_iter___boxed(
    mut v_00_u03b1_2358_: *mut LeanObject,
    mut v_inst_2359_: *mut LeanObject,
    mut v_inst_2360_: *mut LeanObject,
    mut v_r_2361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2362_: *mut LeanObject = core::ptr::null_mut();
    v_res_2362_ = l_Std_Rio_Internal_iter(v_00_u03b1_2358_, v_inst_2359_, v_inst_2360_, v_r_2361_);
    lean_dec_ref(v_inst_2359_);
    return v_res_2362_;
}
pub unsafe fn l_Std_Rio_toList___redArg(
    mut v_inst_2363_: *mut LeanObject,
    mut v_inst_2364_: *mut LeanObject,
    mut v_inst_2365_: *mut LeanObject,
    mut v_r_2366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    v___f_2367_ = lean_alloc_closure(
        l_Std_Rco_toList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2367_, 0, v_inst_2364_);
    lean_closure_set(v___f_2367_, 1, v_inst_2365_);
    v___x_2368_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2368_, 0, v_inst_2363_);
    lean_ctor_set(v___x_2368_, 1, v_r_2366_);
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
    mut v_00_u03b1_2372_: *mut LeanObject,
    mut v_inst_2373_: *mut LeanObject,
    mut v_inst_2374_: *mut LeanObject,
    mut v_inst_2375_: *mut LeanObject,
    mut v_inst_2376_: *mut LeanObject,
    mut v_inst_2377_: *mut LeanObject,
    mut v_inst_2378_: *mut LeanObject,
    mut v_r_2379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    v___f_2380_ = lean_alloc_closure(
        l_Std_Rco_toList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2380_, 0, v_inst_2375_);
    lean_closure_set(v___f_2380_, 1, v_inst_2376_);
    v___x_2381_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2381_, 0, v_inst_2373_);
    lean_ctor_set(v___x_2381_, 1, v_r_2379_);
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
    mut v_inst_2385_: *mut LeanObject,
    mut v_inst_2386_: *mut LeanObject,
    mut v_inst_2387_: *mut LeanObject,
    mut v_r_2388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    v___f_2389_ = lean_alloc_closure(
        l_Std_Rco_toList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2389_, 0, v_inst_2386_);
    lean_closure_set(v___f_2389_, 1, v_inst_2387_);
    v___x_2390_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2390_, 0, v_inst_2385_);
    lean_ctor_set(v___x_2390_, 1, v_r_2388_);
    v___x_2391_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2392_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2389_,
        v___x_2390_,
        v___x_2391_,
    );
    return v___x_2392_;
}
pub unsafe fn l_Std_Rio_toArray(
    mut v_00_u03b1_2393_: *mut LeanObject,
    mut v_inst_2394_: *mut LeanObject,
    mut v_inst_2395_: *mut LeanObject,
    mut v_inst_2396_: *mut LeanObject,
    mut v_inst_2397_: *mut LeanObject,
    mut v_inst_2398_: *mut LeanObject,
    mut v_inst_2399_: *mut LeanObject,
    mut v_r_2400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    v___f_2401_ = lean_alloc_closure(
        l_Std_Rco_toList___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2401_, 0, v_inst_2396_);
    lean_closure_set(v___f_2401_, 1, v_inst_2397_);
    v___x_2402_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2402_, 0, v_inst_2394_);
    lean_ctor_set(v___x_2402_, 1, v_r_2400_);
    v___x_2403_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2404_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2401_,
        v___x_2402_,
        v___x_2403_,
    );
    return v___x_2404_;
}
pub unsafe fn l_Std_Rio_size___redArg(
    mut v_inst_2405_: *mut LeanObject,
    mut v_inst_2406_: *mut LeanObject,
    mut v_r_2407_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_inst_2406_) == 0 {
        let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_r_2407_);
        lean_dec_ref(v_inst_2405_);
        v___x_2408_ = lean_unsigned_to_nat(0);
        return v___x_2408_;
    } else {
        let mut v_val_2409_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
        v_val_2409_ = lean_ctor_get(v_inst_2406_, 0);
        lean_inc(v_val_2409_);
        lean_dec_ref_known(v_inst_2406_, 1);
        v___x_2410_ = lean_apply_2(v_inst_2405_, v_val_2409_, v_r_2407_);
        return v___x_2410_;
    }
}
pub unsafe fn l_Std_Rio_size(
    mut v_00_u03b1_2411_: *mut LeanObject,
    mut v_inst_2412_: *mut LeanObject,
    mut v_inst_2413_: *mut LeanObject,
    mut v_r_2414_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_inst_2413_) == 0 {
        let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_r_2414_);
        lean_dec_ref(v_inst_2412_);
        v___x_2415_ = lean_unsigned_to_nat(0);
        return v___x_2415_;
    } else {
        let mut v_val_2416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
        v_val_2416_ = lean_ctor_get(v_inst_2413_, 0);
        lean_inc(v_val_2416_);
        lean_dec_ref_known(v_inst_2413_, 1);
        v___x_2417_ = lean_apply_2(v_inst_2412_, v_val_2416_, v_r_2414_);
        return v___x_2417_;
    }
}
pub unsafe fn l_Std_Rio_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_2418_: *mut LeanObject,
    mut v_inst_2419_: *mut LeanObject,
    mut v_inst_2420_: *mut LeanObject,
    mut v_inst_2421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2422_: *mut LeanObject = core::ptr::null_mut();
    v___f_2422_ = lean_alloc_closure(l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 8, 4);
    lean_closure_set(v___f_2422_, 0, v_inst_2421_);
    lean_closure_set(v___f_2422_, 1, v_inst_2420_);
    lean_closure_set(v___f_2422_, 2, v_inst_2419_);
    lean_closure_set(v___f_2422_, 3, v_inst_2418_);
    return v___f_2422_;
}
pub unsafe fn l_Std_Rio_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_2423_: *mut LeanObject,
    mut v_m_2424_: *mut LeanObject,
    mut v_inst_2425_: *mut LeanObject,
    mut v_inst_2426_: *mut LeanObject,
    mut v_inst_2427_: *mut LeanObject,
    mut v_inst_2428_: *mut LeanObject,
    mut v_inst_2429_: *mut LeanObject,
    mut v_inst_2430_: *mut LeanObject,
    mut v_inst_2431_: *mut LeanObject,
    mut v_inst_2432_: *mut LeanObject,
    mut v_inst_2433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2434_: *mut LeanObject = core::ptr::null_mut();
    v___f_2434_ = lean_alloc_closure(l_Std_Ric_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 8, 4);
    lean_closure_set(v___f_2434_, 0, v_inst_2432_);
    lean_closure_set(v___f_2434_, 1, v_inst_2428_);
    lean_closure_set(v___f_2434_, 2, v_inst_2427_);
    lean_closure_set(v___f_2434_, 3, v_inst_2425_);
    return v___f_2434_;
}
pub unsafe fn l_Std_Rii_Internal_iter___redArg(
    mut v_inst_2435_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_2435_);
    return v_inst_2435_;
}
pub unsafe fn l_Std_Rii_Internal_iter___redArg___boxed(
    mut v_inst_2436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2437_: *mut LeanObject = core::ptr::null_mut();
    v_res_2437_ = l_Std_Rii_Internal_iter___redArg(v_inst_2436_);
    lean_dec(v_inst_2436_);
    return v_res_2437_;
}
pub unsafe fn l_Std_Rii_Internal_iter(
    mut v_00_u03b1_2438_: *mut LeanObject,
    mut v_inst_2439_: *mut LeanObject,
    mut v_inst_2440_: *mut LeanObject,
    mut v_x_2441_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_2440_);
    return v_inst_2440_;
}
pub unsafe fn l_Std_Rii_Internal_iter___boxed(
    mut v_00_u03b1_2442_: *mut LeanObject,
    mut v_inst_2443_: *mut LeanObject,
    mut v_inst_2444_: *mut LeanObject,
    mut v_x_2445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2446_: *mut LeanObject = core::ptr::null_mut();
    v_res_2446_ = l_Std_Rii_Internal_iter(v_00_u03b1_2442_, v_inst_2443_, v_inst_2444_, v_x_2445_);
    lean_dec(v_inst_2444_);
    lean_dec_ref(v_inst_2443_);
    return v_res_2446_;
}
pub unsafe fn l_Std_Rii_toList___redArg___lam__0(
    mut v_inst_2447_: *mut LeanObject,
    mut v_it_2448_: *mut LeanObject,
    mut v_acc_2449_: *mut LeanObject,
    mut v_recur_2450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_2451_: *mut LeanObject = core::ptr::null_mut();
    v_val_2451_ = lean_apply_1(v_inst_2447_, v_it_2448_);
    match lean_obj_tag(v_val_2451_) {
        0 => {
            let mut v_it_2452_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_2453_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
            v_it_2452_ = lean_ctor_get(v_val_2451_, 0);
            lean_inc(v_it_2452_);
            v_out_2453_ = lean_ctor_get(v_val_2451_, 1);
            lean_inc(v_out_2453_);
            lean_dec_ref_known(v_val_2451_, 2);
            v___x_2454_ = lean_array_push(v_acc_2449_, v_out_2453_);
            v___x_2455_ = lean_apply_3(v_recur_2450_, v_it_2452_, v___x_2454_, lean_box(0));
            return v___x_2455_;
        }
        1 => {
            let mut v_it_2456_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
            v_it_2456_ = lean_ctor_get(v_val_2451_, 0);
            lean_inc(v_it_2456_);
            lean_dec_ref_known(v_val_2451_, 1);
            v___x_2457_ = lean_apply_3(v_recur_2450_, v_it_2456_, v_acc_2449_, lean_box(0));
            return v___x_2457_;
        }
        _ => {
            lean_dec_ref(v_recur_2450_);
            return v_acc_2449_;
        }
    }
}
pub unsafe fn l_Std_Rii_toList___redArg(
    mut v_inst_2458_: *mut LeanObject,
    mut v_inst_2459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    v___f_2460_ = lean_alloc_closure(
        l_Std_Rii_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2460_, 0, v_inst_2459_);
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
    mut v_00_u03b1_2464_: *mut LeanObject,
    mut v_inst_2465_: *mut LeanObject,
    mut v_inst_2466_: *mut LeanObject,
    mut v_r_2467_: *mut LeanObject,
    mut v_inst_2468_: *mut LeanObject,
    mut v_inst_2469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    v___f_2470_ = lean_alloc_closure(
        l_Std_Rii_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2470_, 0, v_inst_2468_);
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
    mut v_00_u03b1_2474_: *mut LeanObject,
    mut v_inst_2475_: *mut LeanObject,
    mut v_inst_2476_: *mut LeanObject,
    mut v_r_2477_: *mut LeanObject,
    mut v_inst_2478_: *mut LeanObject,
    mut v_inst_2479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2480_: *mut LeanObject = core::ptr::null_mut();
    v_res_2480_ = l_Std_Rii_toList(
        v_00_u03b1_2474_,
        v_inst_2475_,
        v_inst_2476_,
        v_r_2477_,
        v_inst_2478_,
        v_inst_2479_,
    );
    lean_dec_ref(v_inst_2475_);
    return v_res_2480_;
}
pub unsafe fn l_Std_Rii_toArray___redArg(
    mut v_inst_2481_: *mut LeanObject,
    mut v_inst_2482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    v___f_2483_ = lean_alloc_closure(
        l_Std_Rii_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2483_, 0, v_inst_2482_);
    v___x_2484_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2485_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2483_,
        v_inst_2481_,
        v___x_2484_,
    );
    return v___x_2485_;
}
pub unsafe fn l_Std_Rii_toArray(
    mut v_00_u03b1_2486_: *mut LeanObject,
    mut v_inst_2487_: *mut LeanObject,
    mut v_inst_2488_: *mut LeanObject,
    mut v_r_2489_: *mut LeanObject,
    mut v_inst_2490_: *mut LeanObject,
    mut v_inst_2491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    v___f_2492_ = lean_alloc_closure(
        l_Std_Rii_toList___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2492_, 0, v_inst_2490_);
    v___x_2493_ = l_Std_Rcc_toList___redArg___closed__0;
    v___x_2494_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_2492_,
        v_inst_2488_,
        v___x_2493_,
    );
    return v___x_2494_;
}
pub unsafe fn l_Std_Rii_toArray___boxed(
    mut v_00_u03b1_2495_: *mut LeanObject,
    mut v_inst_2496_: *mut LeanObject,
    mut v_inst_2497_: *mut LeanObject,
    mut v_r_2498_: *mut LeanObject,
    mut v_inst_2499_: *mut LeanObject,
    mut v_inst_2500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2501_: *mut LeanObject = core::ptr::null_mut();
    v_res_2501_ = l_Std_Rii_toArray(
        v_00_u03b1_2495_,
        v_inst_2496_,
        v_inst_2497_,
        v_r_2498_,
        v_inst_2499_,
        v_inst_2500_,
    );
    lean_dec_ref(v_inst_2496_);
    return v_res_2501_;
}
pub unsafe fn l_Std_Rii_size___redArg(
    mut v_inst_2502_: *mut LeanObject,
    mut v_inst_2503_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_inst_2502_) == 0 {
        let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_2503_);
        v___x_2504_ = lean_unsigned_to_nat(0);
        return v___x_2504_;
    } else {
        let mut v_val_2505_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
        v_val_2505_ = lean_ctor_get(v_inst_2502_, 0);
        lean_inc(v_val_2505_);
        lean_dec_ref_known(v_inst_2502_, 1);
        v___x_2506_ = lean_apply_1(v_inst_2503_, v_val_2505_);
        return v___x_2506_;
    }
}
pub unsafe fn l_Std_Rii_size(
    mut v_00_u03b1_2507_: *mut LeanObject,
    mut v_x_2508_: *mut LeanObject,
    mut v_inst_2509_: *mut LeanObject,
    mut v_inst_2510_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_inst_2509_) == 0 {
        let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_2510_);
        v___x_2511_ = lean_unsigned_to_nat(0);
        return v___x_2511_;
    } else {
        let mut v_val_2512_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
        v_val_2512_ = lean_ctor_get(v_inst_2509_, 0);
        lean_inc(v_val_2512_);
        lean_dec_ref_known(v_inst_2509_, 1);
        v___x_2513_ = lean_apply_1(v_inst_2510_, v_val_2512_);
        return v___x_2513_;
    }
}
pub unsafe fn l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__3(
    mut v_inst_2514_: *mut LeanObject,
    mut v_inst_2515_: *mut LeanObject,
    mut v_inst_2516_: *mut LeanObject,
    mut v_00_u03b2_2517_: *mut LeanObject,
    mut v_r_2518_: *mut LeanObject,
    mut v_init_2519_: *mut LeanObject,
    mut v_f_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2521_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2521_ = lean_ctor_get(v_inst_2514_, 0);
    lean_inc_ref(v_toApplicative_2521_);
    if lean_obj_tag(v_inst_2515_) == 0 {
        let mut v_toPure_2522_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_2520_);
        lean_dec_ref(v_inst_2516_);
        lean_dec_ref(v_inst_2514_);
        v_toPure_2522_ = lean_ctor_get(v_toApplicative_2521_, 1);
        lean_inc(v_toPure_2522_);
        lean_dec_ref(v_toApplicative_2521_);
        v___x_2523_ = lean_apply_2(v_toPure_2522_, lean_box(0), v_init_2519_);
        return v___x_2523_;
    } else {
        let mut v_toBind_2524_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_2525_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_2526_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2527_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2528_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_2524_ = lean_ctor_get(v_inst_2514_, 1);
        lean_inc(v_toBind_2524_);
        lean_dec_ref(v_inst_2514_);
        v_toPure_2525_ = lean_ctor_get(v_toApplicative_2521_, 1);
        lean_inc_n(v_toPure_2525_, 2);
        lean_dec_ref(v_toApplicative_2521_);
        v_val_2526_ = lean_ctor_get(v_inst_2515_, 0);
        lean_inc(v_val_2526_);
        lean_dec_ref_known(v_inst_2515_, 1);
        v___f_2527_ = lean_alloc_closure(l_Std_Rcc_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
        lean_closure_set(v___f_2527_, 0, v_toPure_2525_);
        v___f_2528_ = lean_alloc_closure(l_Std_Rci_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId___redArg___lam__2 as *mut core::ffi::c_void, 9, 5);
        lean_closure_set(v___f_2528_, 0, v_toPure_2525_);
        lean_closure_set(v___f_2528_, 1, v_inst_2516_);
        lean_closure_set(v___f_2528_, 2, v_f_2520_);
        lean_closure_set(v___f_2528_, 3, v_toBind_2524_);
        lean_closure_set(v___f_2528_, 4, v___f_2527_);
        v___x_2529_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_2528_,
            v_val_2526_,
            v_init_2519_,
            lean_box(0),
        );
        return v___x_2529_;
    }
}
pub unsafe fn l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg(
    mut v_inst_2530_: *mut LeanObject,
    mut v_inst_2531_: *mut LeanObject,
    mut v_inst_2532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2533_: *mut LeanObject = core::ptr::null_mut();
    v___f_2533_ = lean_alloc_closure(l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__3 as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___f_2533_, 0, v_inst_2532_);
    lean_closure_set(v___f_2533_, 1, v_inst_2531_);
    lean_closure_set(v___f_2533_, 2, v_inst_2530_);
    return v___f_2533_;
}
pub unsafe fn l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId(
    mut v_00_u03b1_2534_: *mut LeanObject,
    mut v_m_2535_: *mut LeanObject,
    mut v_inst_2536_: *mut LeanObject,
    mut v_inst_2537_: *mut LeanObject,
    mut v_inst_2538_: *mut LeanObject,
    mut v_inst_2539_: *mut LeanObject,
    mut v_inst_2540_: *mut LeanObject,
    mut v_inst_2541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2542_: *mut LeanObject = core::ptr::null_mut();
    v___f_2542_ = lean_alloc_closure(l_Std_Rii_instForIn_x27InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast_x3fOfMonadOfFiniteIteratorId___redArg___lam__3 as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___f_2542_, 0, v_inst_2540_);
    lean_closure_set(v___f_2542_, 1, v_inst_2537_);
    lean_closure_set(v___f_2542_, 2, v_inst_2536_);
    return v___f_2542_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_Iterators(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_Iterators(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Range_Polymorphic_Iterators(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
}
