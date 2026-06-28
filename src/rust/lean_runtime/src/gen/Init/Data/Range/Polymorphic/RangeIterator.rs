// Lean compiler output
// Module: Init.Data.Range.Polymorphic.RangeIterator
// Imports: Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop Init.Data.Range.Polymorphic.PRange Init.Data.Iterators.Consumers.Monadic.Access Init.Data.Iterators.Consumers.Monadic.Loop Init.ByCases Init.Data.Bool Init.Data.List.Lemmas Init.Data.List.Sublist Init.Data.Option.Lemmas
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Access::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Access,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::Data::List::Sublist::{
    initialize_Init_Data_List_Sublist, runtime_initialize_Init_Data_List_Sublist,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Range::Polymorphic::PRange::{
    initialize_Init_Data_Range_Polymorphic_PRange,
    runtime_initialize_Init_Data_Range_Polymorphic_PRange,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_tag, lean_unbox,
};
pub unsafe fn l_Std_Rxc_Iterator_Monadic_step___redArg(
    mut v_inst_1243_: *mut LeanObject,
    mut v_inst_1244_: *mut LeanObject,
    mut v_it_1245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1251_: u8 = 0;
    let mut v_val_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: u8 = 0;
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1259_: u8 = 0;
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1267_: u8 = 0;
    let mut v_unused_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1269_: u8 = 0;
    let mut v_unused_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1246_ = lean_ctor_get(v_it_1245_, 0);
                lean_inc(v_next_1246_);
                if lean_obj_tag(v_next_1246_) == 0 {
                    lean_dec_ref(v_it_1245_);
                    lean_dec_ref(v_inst_1244_);
                    lean_dec_ref(v_inst_1243_);
                    v___x_1247_ = lean_box(2);
                    return v___x_1247_;
                } else {
                    v_upperBound_1248_ = lean_ctor_get(v_it_1245_, 1);
                    v_isSharedCheck_1269_ = (!lean_is_exclusive(v_it_1245_)) as u8;
                    if v_isSharedCheck_1269_ == 0 {
                        v_unused_1270_ = lean_ctor_get(v_it_1245_, 0);
                        lean_dec(v_unused_1270_);
                        v___x_1250_ = v_it_1245_;
                        v_isShared_1251_ = v_isSharedCheck_1269_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_upperBound_1248_);
                        lean_dec(v_it_1245_);
                        v___x_1250_ = lean_box(0);
                        v_isShared_1251_ = v_isSharedCheck_1269_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1252_ = lean_ctor_get(v_next_1246_, 0);
                lean_inc_n(v_val_1252_, 2);
                lean_dec_ref_known(v_next_1246_, 1);
                lean_inc(v_upperBound_1248_);
                v___x_1253_ = lean_apply_2(v_inst_1244_, v_val_1252_, v_upperBound_1248_);
                v___x_1254_ = (lean_unbox(v___x_1253_) as u8);
                if v___x_1254_ == 0 {
                    lean_dec(v_val_1252_);
                    lean_del_object(v___x_1250_);
                    lean_dec(v_upperBound_1248_);
                    lean_dec_ref(v_inst_1243_);
                    v___x_1255_ = lean_box(2);
                    return v___x_1255_;
                } else {
                    v_succ_x3f_1256_ = lean_ctor_get(v_inst_1243_, 0);
                    v_isSharedCheck_1267_ = (!lean_is_exclusive(v_inst_1243_)) as u8;
                    if v_isSharedCheck_1267_ == 0 {
                        v_unused_1268_ = lean_ctor_get(v_inst_1243_, 1);
                        lean_dec(v_unused_1268_);
                        v___x_1258_ = v_inst_1243_;
                        v_isShared_1259_ = v_isSharedCheck_1267_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_succ_x3f_1256_);
                        lean_dec(v_inst_1243_);
                        v___x_1258_ = lean_box(0);
                        v_isShared_1259_ = v_isSharedCheck_1267_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                lean_inc(v_val_1252_);
                v___x_1260_ = lean_apply_1(v_succ_x3f_1256_, v_val_1252_);
                if v_isShared_1251_ == 0 {
                    lean_ctor_set(v___x_1250_, 0, v___x_1260_);
                    v___x_1262_ = v___x_1250_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1260_);
                    lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_upperBound_1248_);
                    v___x_1262_ = v_reuseFailAlloc_1266_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1259_ == 0 {
                    lean_ctor_set(v___x_1258_, 1, v_val_1252_);
                    lean_ctor_set(v___x_1258_, 0, v___x_1262_);
                    v___x_1264_ = v___x_1258_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
                    lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_val_1252_);
                    v___x_1264_ = v_reuseFailAlloc_1265_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1264_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxc_Iterator_Monadic_step(
    mut v_00_u03b1_1271_: *mut LeanObject,
    mut v_inst_1272_: *mut LeanObject,
    mut v_inst_1273_: *mut LeanObject,
    mut v_inst_1274_: *mut LeanObject,
    mut v_it_1275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1281_: u8 = 0;
    let mut v_val_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: u8 = 0;
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1289_: u8 = 0;
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1297_: u8 = 0;
    let mut v_unused_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1299_: u8 = 0;
    let mut v_unused_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1276_ = lean_ctor_get(v_it_1275_, 0);
                lean_inc(v_next_1276_);
                if lean_obj_tag(v_next_1276_) == 0 {
                    lean_dec_ref(v_it_1275_);
                    lean_dec_ref(v_inst_1274_);
                    lean_dec_ref(v_inst_1272_);
                    v___x_1277_ = lean_box(2);
                    return v___x_1277_;
                } else {
                    v_upperBound_1278_ = lean_ctor_get(v_it_1275_, 1);
                    v_isSharedCheck_1299_ = (!lean_is_exclusive(v_it_1275_)) as u8;
                    if v_isSharedCheck_1299_ == 0 {
                        v_unused_1300_ = lean_ctor_get(v_it_1275_, 0);
                        lean_dec(v_unused_1300_);
                        v___x_1280_ = v_it_1275_;
                        v_isShared_1281_ = v_isSharedCheck_1299_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_upperBound_1278_);
                        lean_dec(v_it_1275_);
                        v___x_1280_ = lean_box(0);
                        v_isShared_1281_ = v_isSharedCheck_1299_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1282_ = lean_ctor_get(v_next_1276_, 0);
                lean_inc_n(v_val_1282_, 2);
                lean_dec_ref_known(v_next_1276_, 1);
                lean_inc(v_upperBound_1278_);
                v___x_1283_ = lean_apply_2(v_inst_1274_, v_val_1282_, v_upperBound_1278_);
                v___x_1284_ = (lean_unbox(v___x_1283_) as u8);
                if v___x_1284_ == 0 {
                    lean_dec(v_val_1282_);
                    lean_del_object(v___x_1280_);
                    lean_dec(v_upperBound_1278_);
                    lean_dec_ref(v_inst_1272_);
                    v___x_1285_ = lean_box(2);
                    return v___x_1285_;
                } else {
                    v_succ_x3f_1286_ = lean_ctor_get(v_inst_1272_, 0);
                    v_isSharedCheck_1297_ = (!lean_is_exclusive(v_inst_1272_)) as u8;
                    if v_isSharedCheck_1297_ == 0 {
                        v_unused_1298_ = lean_ctor_get(v_inst_1272_, 1);
                        lean_dec(v_unused_1298_);
                        v___x_1288_ = v_inst_1272_;
                        v_isShared_1289_ = v_isSharedCheck_1297_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_succ_x3f_1286_);
                        lean_dec(v_inst_1272_);
                        v___x_1288_ = lean_box(0);
                        v_isShared_1289_ = v_isSharedCheck_1297_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                lean_inc(v_val_1282_);
                v___x_1290_ = lean_apply_1(v_succ_x3f_1286_, v_val_1282_);
                if v_isShared_1281_ == 0 {
                    lean_ctor_set(v___x_1280_, 0, v___x_1290_);
                    v___x_1292_ = v___x_1280_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1290_);
                    lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_upperBound_1278_);
                    v___x_1292_ = v_reuseFailAlloc_1296_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1289_ == 0 {
                    lean_ctor_set(v___x_1288_, 1, v_val_1282_);
                    lean_ctor_set(v___x_1288_, 0, v___x_1292_);
                    v___x_1294_ = v___x_1288_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
                    lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_val_1282_);
                    v___x_1294_ = v_reuseFailAlloc_1295_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxc_Iterator_step___redArg(
    mut v_inst_1301_: *mut LeanObject,
    mut v_inst_1302_: *mut LeanObject,
    mut v_it_1303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1309_: u8 = 0;
    let mut v_val_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: u8 = 0;
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1317_: u8 = 0;
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1325_: u8 = 0;
    let mut v_unused_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1327_: u8 = 0;
    let mut v_unused_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1304_ = lean_ctor_get(v_it_1303_, 0);
                lean_inc(v_next_1304_);
                if lean_obj_tag(v_next_1304_) == 0 {
                    lean_dec_ref(v_it_1303_);
                    lean_dec_ref(v_inst_1302_);
                    lean_dec_ref(v_inst_1301_);
                    v___x_1305_ = lean_box(2);
                    return v___x_1305_;
                } else {
                    v_upperBound_1306_ = lean_ctor_get(v_it_1303_, 1);
                    v_isSharedCheck_1327_ = (!lean_is_exclusive(v_it_1303_)) as u8;
                    if v_isSharedCheck_1327_ == 0 {
                        v_unused_1328_ = lean_ctor_get(v_it_1303_, 0);
                        lean_dec(v_unused_1328_);
                        v___x_1308_ = v_it_1303_;
                        v_isShared_1309_ = v_isSharedCheck_1327_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_upperBound_1306_);
                        lean_dec(v_it_1303_);
                        v___x_1308_ = lean_box(0);
                        v_isShared_1309_ = v_isSharedCheck_1327_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1310_ = lean_ctor_get(v_next_1304_, 0);
                lean_inc_n(v_val_1310_, 2);
                lean_dec_ref_known(v_next_1304_, 1);
                lean_inc(v_upperBound_1306_);
                v___x_1311_ = lean_apply_2(v_inst_1302_, v_val_1310_, v_upperBound_1306_);
                v___x_1312_ = (lean_unbox(v___x_1311_) as u8);
                if v___x_1312_ == 0 {
                    lean_dec(v_val_1310_);
                    lean_del_object(v___x_1308_);
                    lean_dec(v_upperBound_1306_);
                    lean_dec_ref(v_inst_1301_);
                    v___x_1313_ = lean_box(2);
                    return v___x_1313_;
                } else {
                    v_succ_x3f_1314_ = lean_ctor_get(v_inst_1301_, 0);
                    v_isSharedCheck_1325_ = (!lean_is_exclusive(v_inst_1301_)) as u8;
                    if v_isSharedCheck_1325_ == 0 {
                        v_unused_1326_ = lean_ctor_get(v_inst_1301_, 1);
                        lean_dec(v_unused_1326_);
                        v___x_1316_ = v_inst_1301_;
                        v_isShared_1317_ = v_isSharedCheck_1325_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_succ_x3f_1314_);
                        lean_dec(v_inst_1301_);
                        v___x_1316_ = lean_box(0);
                        v_isShared_1317_ = v_isSharedCheck_1325_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                lean_inc(v_val_1310_);
                v___x_1318_ = lean_apply_1(v_succ_x3f_1314_, v_val_1310_);
                if v_isShared_1309_ == 0 {
                    lean_ctor_set(v___x_1308_, 0, v___x_1318_);
                    v___x_1320_ = v___x_1308_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1318_);
                    lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_upperBound_1306_);
                    v___x_1320_ = v_reuseFailAlloc_1324_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1317_ == 0 {
                    lean_ctor_set(v___x_1316_, 1, v_val_1310_);
                    lean_ctor_set(v___x_1316_, 0, v___x_1320_);
                    v___x_1322_ = v___x_1316_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
                    lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_val_1310_);
                    v___x_1322_ = v_reuseFailAlloc_1323_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1322_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxc_Iterator_step(
    mut v_00_u03b1_1329_: *mut LeanObject,
    mut v_inst_1330_: *mut LeanObject,
    mut v_inst_1331_: *mut LeanObject,
    mut v_inst_1332_: *mut LeanObject,
    mut v_it_1333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1339_: u8 = 0;
    let mut v_val_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1355_: u8 = 0;
    let mut v_unused_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1357_: u8 = 0;
    let mut v_unused_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1334_ = lean_ctor_get(v_it_1333_, 0);
                lean_inc(v_next_1334_);
                if lean_obj_tag(v_next_1334_) == 0 {
                    lean_dec_ref(v_it_1333_);
                    lean_dec_ref(v_inst_1332_);
                    lean_dec_ref(v_inst_1330_);
                    v___x_1335_ = lean_box(2);
                    return v___x_1335_;
                } else {
                    v_upperBound_1336_ = lean_ctor_get(v_it_1333_, 1);
                    v_isSharedCheck_1357_ = (!lean_is_exclusive(v_it_1333_)) as u8;
                    if v_isSharedCheck_1357_ == 0 {
                        v_unused_1358_ = lean_ctor_get(v_it_1333_, 0);
                        lean_dec(v_unused_1358_);
                        v___x_1338_ = v_it_1333_;
                        v_isShared_1339_ = v_isSharedCheck_1357_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_upperBound_1336_);
                        lean_dec(v_it_1333_);
                        v___x_1338_ = lean_box(0);
                        v_isShared_1339_ = v_isSharedCheck_1357_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1340_ = lean_ctor_get(v_next_1334_, 0);
                lean_inc_n(v_val_1340_, 2);
                lean_dec_ref_known(v_next_1334_, 1);
                lean_inc(v_upperBound_1336_);
                v___x_1341_ = lean_apply_2(v_inst_1332_, v_val_1340_, v_upperBound_1336_);
                v___x_1342_ = (lean_unbox(v___x_1341_) as u8);
                if v___x_1342_ == 0 {
                    lean_dec(v_val_1340_);
                    lean_del_object(v___x_1338_);
                    lean_dec(v_upperBound_1336_);
                    lean_dec_ref(v_inst_1330_);
                    v___x_1343_ = lean_box(2);
                    return v___x_1343_;
                } else {
                    v_succ_x3f_1344_ = lean_ctor_get(v_inst_1330_, 0);
                    v_isSharedCheck_1355_ = (!lean_is_exclusive(v_inst_1330_)) as u8;
                    if v_isSharedCheck_1355_ == 0 {
                        v_unused_1356_ = lean_ctor_get(v_inst_1330_, 1);
                        lean_dec(v_unused_1356_);
                        v___x_1346_ = v_inst_1330_;
                        v_isShared_1347_ = v_isSharedCheck_1355_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_succ_x3f_1344_);
                        lean_dec(v_inst_1330_);
                        v___x_1346_ = lean_box(0);
                        v_isShared_1347_ = v_isSharedCheck_1355_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                lean_inc(v_val_1340_);
                v___x_1348_ = lean_apply_1(v_succ_x3f_1344_, v_val_1340_);
                if v_isShared_1339_ == 0 {
                    lean_ctor_set(v___x_1338_, 0, v___x_1348_);
                    v___x_1350_ = v___x_1338_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1348_);
                    lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_upperBound_1336_);
                    v___x_1350_ = v_reuseFailAlloc_1354_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1347_ == 0 {
                    lean_ctor_set(v___x_1346_, 1, v_val_1340_);
                    lean_ctor_set(v___x_1346_, 0, v___x_1350_);
                    v___x_1352_ = v___x_1346_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
                    lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_val_1340_);
                    v___x_1352_ = v_reuseFailAlloc_1353_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1352_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter___redArg(
    mut v_x_1359_: *mut LeanObject,
    mut v_h__1_1360_: *mut LeanObject,
    mut v_h__2_1361_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1359_) == 0 {
        let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1361_);
        v___x_1362_ = lean_box(0);
        v___x_1363_ = lean_apply_1(v_h__1_1360_, v___x_1362_);
        return v___x_1363_;
    } else {
        let mut v_val_1364_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1360_);
        v_val_1364_ = lean_ctor_get(v_x_1359_, 0);
        lean_inc(v_val_1364_);
        lean_dec_ref_known(v_x_1359_, 1);
        v___x_1365_ = lean_apply_1(v_h__2_1361_, v_val_1364_);
        return v___x_1365_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter(
    mut v_00_u03b1_1366_: *mut LeanObject,
    mut v_motive_1367_: *mut LeanObject,
    mut v_x_1368_: *mut LeanObject,
    mut v_h__1_1369_: *mut LeanObject,
    mut v_h__2_1370_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1368_) == 0 {
        let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1370_);
        v___x_1371_ = lean_box(0);
        v___x_1372_ = lean_apply_1(v_h__1_1369_, v___x_1371_);
        return v___x_1372_;
    } else {
        let mut v_val_1373_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1369_);
        v_val_1373_ = lean_ctor_get(v_x_1368_, 0);
        lean_inc(v_val_1373_);
        lean_dec_ref_known(v_x_1368_, 1);
        v___x_1374_ = lean_apply_1(v_h__2_1370_, v_val_1373_);
        return v___x_1374_;
    }
}
pub unsafe fn l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg___lam__0(
    mut v_inst_1375_: *mut LeanObject,
    mut v_inst_1376_: *mut LeanObject,
    mut v_it_1377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1383_: u8 = 0;
    let mut v_val_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: u8 = 0;
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1391_: u8 = 0;
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1399_: u8 = 0;
    let mut v_unused_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1401_: u8 = 0;
    let mut v_unused_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1378_ = lean_ctor_get(v_it_1377_, 0);
                lean_inc(v_next_1378_);
                if lean_obj_tag(v_next_1378_) == 0 {
                    lean_dec_ref(v_it_1377_);
                    lean_dec_ref(v_inst_1376_);
                    lean_dec_ref(v_inst_1375_);
                    v___x_1379_ = lean_box(2);
                    return v___x_1379_;
                } else {
                    v_upperBound_1380_ = lean_ctor_get(v_it_1377_, 1);
                    v_isSharedCheck_1401_ = (!lean_is_exclusive(v_it_1377_)) as u8;
                    if v_isSharedCheck_1401_ == 0 {
                        v_unused_1402_ = lean_ctor_get(v_it_1377_, 0);
                        lean_dec(v_unused_1402_);
                        v___x_1382_ = v_it_1377_;
                        v_isShared_1383_ = v_isSharedCheck_1401_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_upperBound_1380_);
                        lean_dec(v_it_1377_);
                        v___x_1382_ = lean_box(0);
                        v_isShared_1383_ = v_isSharedCheck_1401_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1384_ = lean_ctor_get(v_next_1378_, 0);
                lean_inc_n(v_val_1384_, 2);
                lean_dec_ref_known(v_next_1378_, 1);
                lean_inc(v_upperBound_1380_);
                v___x_1385_ = lean_apply_2(v_inst_1375_, v_val_1384_, v_upperBound_1380_);
                v___x_1386_ = (lean_unbox(v___x_1385_) as u8);
                if v___x_1386_ == 0 {
                    lean_dec(v_val_1384_);
                    lean_del_object(v___x_1382_);
                    lean_dec(v_upperBound_1380_);
                    lean_dec_ref(v_inst_1376_);
                    v___x_1387_ = lean_box(2);
                    return v___x_1387_;
                } else {
                    v_succ_x3f_1388_ = lean_ctor_get(v_inst_1376_, 0);
                    v_isSharedCheck_1399_ = (!lean_is_exclusive(v_inst_1376_)) as u8;
                    if v_isSharedCheck_1399_ == 0 {
                        v_unused_1400_ = lean_ctor_get(v_inst_1376_, 1);
                        lean_dec(v_unused_1400_);
                        v___x_1390_ = v_inst_1376_;
                        v_isShared_1391_ = v_isSharedCheck_1399_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_succ_x3f_1388_);
                        lean_dec(v_inst_1376_);
                        v___x_1390_ = lean_box(0);
                        v_isShared_1391_ = v_isSharedCheck_1399_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                lean_inc(v_val_1384_);
                v___x_1392_ = lean_apply_1(v_succ_x3f_1388_, v_val_1384_);
                if v_isShared_1383_ == 0 {
                    lean_ctor_set(v___x_1382_, 0, v___x_1392_);
                    v___x_1394_ = v___x_1382_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1392_);
                    lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_upperBound_1380_);
                    v___x_1394_ = v_reuseFailAlloc_1398_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1391_ == 0 {
                    lean_ctor_set(v___x_1390_, 1, v_val_1384_);
                    lean_ctor_set(v___x_1390_, 0, v___x_1394_);
                    v___x_1396_ = v___x_1390_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_val_1384_);
                    v___x_1396_ = v_reuseFailAlloc_1397_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg(
    mut v_inst_1403_: *mut LeanObject,
    mut v_inst_1404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1405_: *mut LeanObject = core::ptr::null_mut();
    v___f_1405_ = lean_alloc_closure(
        l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1405_, 0, v_inst_1404_);
    lean_closure_set(v___f_1405_, 1, v_inst_1403_);
    return v___f_1405_;
}
pub unsafe fn l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE(
    mut v_00_u03b1_1406_: *mut LeanObject,
    mut v_inst_1407_: *mut LeanObject,
    mut v_inst_1408_: *mut LeanObject,
    mut v_inst_1409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1410_: *mut LeanObject = core::ptr::null_mut();
    v___f_1410_ = lean_alloc_closure(
        l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1410_, 0, v_inst_1409_);
    lean_closure_set(v___f_1410_, 1, v_inst_1407_);
    return v___f_1410_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterStep_successor_match__1_splitter___redArg(
    mut v_x_1411_: *mut LeanObject,
    mut v_h__1_1412_: *mut LeanObject,
    mut v_h__2_1413_: *mut LeanObject,
    mut v_h__3_1414_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1411_) {
        0 => {
            let mut v_it_1415_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_1416_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1414_);
            lean_dec(v_h__2_1413_);
            v_it_1415_ = lean_ctor_get(v_x_1411_, 0);
            lean_inc(v_it_1415_);
            v_out_1416_ = lean_ctor_get(v_x_1411_, 1);
            lean_inc(v_out_1416_);
            lean_dec_ref_known(v_x_1411_, 2);
            v___x_1417_ = lean_apply_2(v_h__1_1412_, v_it_1415_, v_out_1416_);
            return v___x_1417_;
        }
        1 => {
            let mut v_it_1418_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1414_);
            lean_dec(v_h__1_1412_);
            v_it_1418_ = lean_ctor_get(v_x_1411_, 0);
            lean_inc(v_it_1418_);
            lean_dec_ref_known(v_x_1411_, 1);
            v___x_1419_ = lean_apply_1(v_h__2_1413_, v_it_1418_);
            return v___x_1419_;
        }
        _ => {
            let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1413_);
            lean_dec(v_h__1_1412_);
            v___x_1420_ = lean_box(0);
            v___x_1421_ = lean_apply_1(v_h__3_1414_, v___x_1420_);
            return v___x_1421_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterStep_successor_match__1_splitter(
    mut v_00_u03b1_1422_: *mut LeanObject,
    mut v_00_u03b2_1423_: *mut LeanObject,
    mut v_motive_1424_: *mut LeanObject,
    mut v_x_1425_: *mut LeanObject,
    mut v_h__1_1426_: *mut LeanObject,
    mut v_h__2_1427_: *mut LeanObject,
    mut v_h__3_1428_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1425_) {
        0 => {
            let mut v_it_1429_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_1430_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1428_);
            lean_dec(v_h__2_1427_);
            v_it_1429_ = lean_ctor_get(v_x_1425_, 0);
            lean_inc(v_it_1429_);
            v_out_1430_ = lean_ctor_get(v_x_1425_, 1);
            lean_inc(v_out_1430_);
            lean_dec_ref_known(v_x_1425_, 2);
            v___x_1431_ = lean_apply_2(v_h__1_1426_, v_it_1429_, v_out_1430_);
            return v___x_1431_;
        }
        1 => {
            let mut v_it_1432_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1428_);
            lean_dec(v_h__1_1426_);
            v_it_1432_ = lean_ctor_get(v_x_1425_, 0);
            lean_inc(v_it_1432_);
            lean_dec_ref_known(v_x_1425_, 1);
            v___x_1433_ = lean_apply_1(v_h__2_1427_, v_it_1432_);
            return v___x_1433_;
        }
        _ => {
            let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1427_);
            lean_dec(v_h__1_1426_);
            v___x_1434_ = lean_box(0);
            v___x_1435_ = lean_apply_1(v_h__3_1428_, v___x_1434_);
            return v___x_1435_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation(
    mut v_00_u03b1_1436_: *mut LeanObject,
    mut v_inst_1437_: *mut LeanObject,
    mut v_inst_1438_: *mut LeanObject,
    mut v_inst_1439_: *mut LeanObject,
    mut v_inst_1440_: *mut LeanObject,
    mut v_inst_1441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    v___x_1442_ = lean_box(0);
    return v___x_1442_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___boxed(
    mut v_00_u03b1_1443_: *mut LeanObject,
    mut v_inst_1444_: *mut LeanObject,
    mut v_inst_1445_: *mut LeanObject,
    mut v_inst_1446_: *mut LeanObject,
    mut v_inst_1447_: *mut LeanObject,
    mut v_inst_1448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1449_: *mut LeanObject = core::ptr::null_mut();
    v_res_1449_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation(v_00_u03b1_1443_, v_inst_1444_, v_inst_1445_, v_inst_1446_, v_inst_1447_, v_inst_1448_);
    lean_dec_ref(v_inst_1446_);
    lean_dec_ref(v_inst_1444_);
    return v_res_1449_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation(
    mut v_00_u03b1_1450_: *mut LeanObject,
    mut v_inst_1451_: *mut LeanObject,
    mut v_inst_1452_: *mut LeanObject,
    mut v_inst_1453_: *mut LeanObject,
    mut v_inst_1454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    v___x_1455_ = lean_box(0);
    return v___x_1455_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___boxed(
    mut v_00_u03b1_1456_: *mut LeanObject,
    mut v_inst_1457_: *mut LeanObject,
    mut v_inst_1458_: *mut LeanObject,
    mut v_inst_1459_: *mut LeanObject,
    mut v_inst_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1461_: *mut LeanObject = core::ptr::null_mut();
    v_res_1461_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation(v_00_u03b1_1456_, v_inst_1457_, v_inst_1458_, v_inst_1459_, v_inst_1460_);
    lean_dec_ref(v_inst_1459_);
    lean_dec_ref(v_inst_1457_);
    return v_res_1461_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorAccess_match__1_splitter___redArg(
    mut v_x_1462_: *mut LeanObject,
    mut v_h__1_1463_: *mut LeanObject,
    mut v_h__2_1464_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1462_) == 0 {
        let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1464_);
        v___x_1465_ = lean_box(0);
        v___x_1466_ = lean_apply_1(v_h__1_1463_, v___x_1465_);
        return v___x_1466_;
    } else {
        let mut v_val_1467_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1463_);
        v_val_1467_ = lean_ctor_get(v_x_1462_, 0);
        lean_inc(v_val_1467_);
        lean_dec_ref_known(v_x_1462_, 1);
        v___x_1468_ = lean_apply_1(v_h__2_1464_, v_val_1467_);
        return v___x_1468_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorAccess_match__1_splitter(
    mut v_00_u03b1_1469_: *mut LeanObject,
    mut v_motive_1470_: *mut LeanObject,
    mut v_x_1471_: *mut LeanObject,
    mut v_h__1_1472_: *mut LeanObject,
    mut v_h__2_1473_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1471_) == 0 {
        let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1473_);
        v___x_1474_ = lean_box(0);
        v___x_1475_ = lean_apply_1(v_h__1_1472_, v___x_1474_);
        return v___x_1475_;
    } else {
        let mut v_val_1476_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1472_);
        v_val_1476_ = lean_ctor_get(v_x_1471_, 0);
        lean_inc(v_val_1476_);
        lean_dec_ref_known(v_x_1471_, 1);
        v___x_1477_ = lean_apply_1(v_h__2_1473_, v_val_1476_);
        return v___x_1477_;
    }
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0(
    mut v_inst_1478_: *mut LeanObject,
    mut v_inst_1479_: *mut LeanObject,
    mut v_it_1480_: *mut LeanObject,
    mut v_n_1481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1487_: u8 = 0;
    let mut v_succ_x3f_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succMany_x3f_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v_val_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: u8 = 0;
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1507_: u8 = 0;
    let mut v_isSharedCheck_1508_: u8 = 0;
    let mut v_unused_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1482_ = lean_ctor_get(v_it_1480_, 0);
                lean_inc(v_next_1482_);
                if lean_obj_tag(v_next_1482_) == 0 {
                    lean_dec(v_n_1481_);
                    lean_dec_ref(v_it_1480_);
                    lean_dec_ref(v_inst_1479_);
                    lean_dec_ref(v_inst_1478_);
                    v___x_1483_ = lean_box(2);
                    return v___x_1483_;
                } else {
                    v_upperBound_1484_ = lean_ctor_get(v_it_1480_, 1);
                    v_isSharedCheck_1508_ = (!lean_is_exclusive(v_it_1480_)) as u8;
                    if v_isSharedCheck_1508_ == 0 {
                        v_unused_1509_ = lean_ctor_get(v_it_1480_, 0);
                        lean_dec(v_unused_1509_);
                        v___x_1486_ = v_it_1480_;
                        v_isShared_1487_ = v_isSharedCheck_1508_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_upperBound_1484_);
                        lean_dec(v_it_1480_);
                        v___x_1486_ = lean_box(0);
                        v_isShared_1487_ = v_isSharedCheck_1508_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_succ_x3f_1488_ = lean_ctor_get(v_inst_1478_, 0);
                v_succMany_x3f_1489_ = lean_ctor_get(v_inst_1478_, 1);
                v_isSharedCheck_1507_ = (!lean_is_exclusive(v_inst_1478_)) as u8;
                if v_isSharedCheck_1507_ == 0 {
                    v___x_1491_ = v_inst_1478_;
                    v_isShared_1492_ = v_isSharedCheck_1507_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_succMany_x3f_1489_);
                    lean_inc(v_succ_x3f_1488_);
                    lean_dec(v_inst_1478_);
                    v___x_1491_ = lean_box(0);
                    v_isShared_1492_ = v_isSharedCheck_1507_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_val_1493_ = lean_ctor_get(v_next_1482_, 0);
                lean_inc(v_val_1493_);
                lean_dec_ref_known(v_next_1482_, 1);
                v___x_1494_ = lean_apply_2(v_succMany_x3f_1489_, v_n_1481_, v_val_1493_);
                if lean_obj_tag(v___x_1494_) == 0 {
                    lean_del_object(v___x_1491_);
                    lean_dec_ref(v_succ_x3f_1488_);
                    lean_del_object(v___x_1486_);
                    lean_dec(v_upperBound_1484_);
                    lean_dec_ref(v_inst_1479_);
                    v___x_1495_ = lean_box(2);
                    return v___x_1495_;
                } else {
                    v_val_1496_ = lean_ctor_get(v___x_1494_, 0);
                    lean_inc_n(v_val_1496_, 2);
                    lean_dec_ref_known(v___x_1494_, 1);
                    lean_inc(v_upperBound_1484_);
                    v___x_1497_ = lean_apply_2(v_inst_1479_, v_val_1496_, v_upperBound_1484_);
                    v___x_1498_ = (lean_unbox(v___x_1497_) as u8);
                    if v___x_1498_ == 0 {
                        lean_dec(v_val_1496_);
                        lean_del_object(v___x_1491_);
                        lean_dec_ref(v_succ_x3f_1488_);
                        lean_del_object(v___x_1486_);
                        lean_dec(v_upperBound_1484_);
                        v___x_1499_ = lean_box(2);
                        return v___x_1499_;
                    } else {
                        lean_inc(v_val_1496_);
                        v___x_1500_ = lean_apply_1(v_succ_x3f_1488_, v_val_1496_);
                        if v_isShared_1487_ == 0 {
                            lean_ctor_set(v___x_1486_, 0, v___x_1500_);
                            v___x_1502_ = v___x_1486_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1500_);
                            lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_upperBound_1484_);
                            v___x_1502_ = v_reuseFailAlloc_1506_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_1492_ == 0 {
                    lean_ctor_set(v___x_1491_, 1, v_val_1496_);
                    lean_ctor_set(v___x_1491_, 0, v___x_1502_);
                    v___x_1504_ = v___x_1491_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
                    lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_val_1496_);
                    v___x_1504_ = v_reuseFailAlloc_1505_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorAccess___redArg(
    mut v_inst_1510_: *mut LeanObject,
    mut v_inst_1511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1512_: *mut LeanObject = core::ptr::null_mut();
    v___f_1512_ = lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1512_, 0, v_inst_1510_);
    lean_closure_set(v___f_1512_, 1, v_inst_1511_);
    return v___f_1512_;
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorAccess(
    mut v_00_u03b1_1513_: *mut LeanObject,
    mut v_inst_1514_: *mut LeanObject,
    mut v_inst_1515_: *mut LeanObject,
    mut v_inst_1516_: *mut LeanObject,
    mut v_inst_1517_: *mut LeanObject,
    mut v_inst_1518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1519_: *mut LeanObject = core::ptr::null_mut();
    v___f_1519_ = lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1519_, 0, v_inst_1514_);
    lean_closure_set(v___f_1519_, 1, v_inst_1516_);
    return v___f_1519_;
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0(
    mut v_toApplicative_1520_: *mut LeanObject,
    mut v_inst_1521_: *mut LeanObject,
    mut v_next_1522_: *mut LeanObject,
    mut v_G_1523_: *mut LeanObject,
    mut v_____do__lift_1524_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1524_) == 0 {
        let mut v_a_1525_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1526_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_G_1523_);
        lean_dec(v_next_1522_);
        lean_dec_ref(v_inst_1521_);
        v_a_1525_ = lean_ctor_get(v_____do__lift_1524_, 0);
        lean_inc(v_a_1525_);
        lean_dec_ref_known(v_____do__lift_1524_, 1);
        v_toPure_1526_ = lean_ctor_get(v_toApplicative_1520_, 1);
        lean_inc(v_toPure_1526_);
        lean_dec_ref(v_toApplicative_1520_);
        v___x_1527_ = lean_apply_2(v_toPure_1526_, lean_box(0), v_a_1525_);
        return v___x_1527_;
    } else {
        let mut v_a_1528_: *mut LeanObject = core::ptr::null_mut();
        let mut v_succ_x3f_1529_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
        v_a_1528_ = lean_ctor_get(v_____do__lift_1524_, 0);
        lean_inc(v_a_1528_);
        lean_dec_ref_known(v_____do__lift_1524_, 1);
        v_succ_x3f_1529_ = lean_ctor_get(v_inst_1521_, 0);
        lean_inc_ref(v_succ_x3f_1529_);
        lean_dec_ref(v_inst_1521_);
        v___x_1530_ = lean_apply_1(v_succ_x3f_1529_, v_next_1522_);
        if lean_obj_tag(v___x_1530_) == 0 {
            let mut v_toPure_1531_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_G_1523_);
            v_toPure_1531_ = lean_ctor_get(v_toApplicative_1520_, 1);
            lean_inc(v_toPure_1531_);
            lean_dec_ref(v_toApplicative_1520_);
            v___x_1532_ = lean_apply_2(v_toPure_1531_, lean_box(0), v_a_1528_);
            return v___x_1532_;
        } else {
            let mut v_val_1533_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_toApplicative_1520_);
            v_val_1533_ = lean_ctor_get(v___x_1530_, 0);
            lean_inc(v_val_1533_);
            lean_dec_ref_known(v___x_1530_, 1);
            v___x_1534_ = lean_apply_4(v_G_1523_, v_val_1533_, v_a_1528_, lean_box(0), lean_box(0));
            return v___x_1534_;
        }
    }
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1(
    mut v_inst_1535_: *mut LeanObject,
    mut v_upperBound_1536_: *mut LeanObject,
    mut v_inst_1537_: *mut LeanObject,
    mut v_inst_1538_: *mut LeanObject,
    mut v_f_1539_: *mut LeanObject,
    mut v_next_1540_: *mut LeanObject,
    mut v_acc_1541_: *mut LeanObject,
    mut v_h_1542_: *mut LeanObject,
    mut v_G_1543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: u8 = 0;
    lean_inc(v_next_1540_);
    v___x_1544_ = lean_apply_2(v_inst_1535_, v_next_1540_, v_upperBound_1536_);
    v___x_1545_ = (lean_unbox(v___x_1544_) as u8);
    if v___x_1545_ == 0 {
        let mut v_toApplicative_1546_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1547_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_G_1543_);
        lean_dec(v_next_1540_);
        lean_dec(v_f_1539_);
        lean_dec_ref(v_inst_1538_);
        v_toApplicative_1546_ = lean_ctor_get(v_inst_1537_, 0);
        lean_inc_ref(v_toApplicative_1546_);
        lean_dec_ref(v_inst_1537_);
        v_toPure_1547_ = lean_ctor_get(v_toApplicative_1546_, 1);
        lean_inc(v_toPure_1547_);
        lean_dec_ref(v_toApplicative_1546_);
        v___x_1548_ = lean_apply_2(v_toPure_1547_, lean_box(0), v_acc_1541_);
        return v___x_1548_;
    } else {
        let mut v_toApplicative_1549_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_1550_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1551_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1549_ = lean_ctor_get(v_inst_1537_, 0);
        lean_inc_ref(v_toApplicative_1549_);
        v_toBind_1550_ = lean_ctor_get(v_inst_1537_, 1);
        lean_inc(v_toBind_1550_);
        lean_dec_ref(v_inst_1537_);
        lean_inc(v_next_1540_);
        v___f_1551_ = lean_alloc_closure(
            l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1551_, 0, v_toApplicative_1549_);
        lean_closure_set(v___f_1551_, 1, v_inst_1538_);
        lean_closure_set(v___f_1551_, 2, v_next_1540_);
        lean_closure_set(v___f_1551_, 3, v_G_1543_);
        v___x_1552_ = lean_apply_4(
            v_f_1539_,
            v_next_1540_,
            lean_box(0),
            lean_box(0),
            v_acc_1541_,
        );
        v___x_1553_ = lean_apply_4(
            v_toBind_1550_,
            lean_box(0),
            lean_box(0),
            v___x_1552_,
            v___f_1551_,
        );
        return v___x_1553_;
    }
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg(
    mut v_inst_1554_: *mut LeanObject,
    mut v_inst_1555_: *mut LeanObject,
    mut v_inst_1556_: *mut LeanObject,
    mut v_upperBound_1557_: *mut LeanObject,
    mut v_acc_1558_: *mut LeanObject,
    mut v_next_1559_: *mut LeanObject,
    mut v_f_1560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    v___f_1561_ = lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1 as *mut core::ffi::c_void,
        9,
        5,
    );
    lean_closure_set(v___f_1561_, 0, v_inst_1555_);
    lean_closure_set(v___f_1561_, 1, v_upperBound_1557_);
    lean_closure_set(v___f_1561_, 2, v_inst_1556_);
    lean_closure_set(v___f_1561_, 3, v_inst_1554_);
    lean_closure_set(v___f_1561_, 4, v_f_1560_);
    v___x_1562_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1561_, v_next_1559_, v_acc_1558_, lean_box(0));
    return v___x_1562_;
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop_loop(
    mut v_00_u03b1_1563_: *mut LeanObject,
    mut v_inst_1564_: *mut LeanObject,
    mut v_inst_1565_: *mut LeanObject,
    mut v_inst_1566_: *mut LeanObject,
    mut v_inst_1567_: *mut LeanObject,
    mut v_inst_1568_: *mut LeanObject,
    mut v_n_1569_: *mut LeanObject,
    mut v_inst_1570_: *mut LeanObject,
    mut v_00_u03b3_1571_: *mut LeanObject,
    mut v_Pl_1572_: *mut LeanObject,
    mut v_LargeEnough_1573_: *mut LeanObject,
    mut v_hl_1574_: *mut LeanObject,
    mut v_upperBound_1575_: *mut LeanObject,
    mut v_acc_1576_: *mut LeanObject,
    mut v_next_1577_: *mut LeanObject,
    mut v_h_1578_: *mut LeanObject,
    mut v_f_1579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    v___f_1580_ = lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1 as *mut core::ffi::c_void,
        9,
        5,
    );
    lean_closure_set(v___f_1580_, 0, v_inst_1566_);
    lean_closure_set(v___f_1580_, 1, v_upperBound_1575_);
    lean_closure_set(v___f_1580_, 2, v_inst_1570_);
    lean_closure_set(v___f_1580_, 3, v_inst_1564_);
    lean_closure_set(v___f_1580_, 4, v_f_1579_);
    v___x_1581_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1580_, v_next_1577_, v_acc_1576_, lean_box(0));
    return v___x_1581_;
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop_loop___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03b1_1582_: *mut LeanObject = *_args.add(0);
    let mut v_inst_1583_: *mut LeanObject = *_args.add(1);
    let mut v_inst_1584_: *mut LeanObject = *_args.add(2);
    let mut v_inst_1585_: *mut LeanObject = *_args.add(3);
    let mut v_inst_1586_: *mut LeanObject = *_args.add(4);
    let mut v_inst_1587_: *mut LeanObject = *_args.add(5);
    let mut v_n_1588_: *mut LeanObject = *_args.add(6);
    let mut v_inst_1589_: *mut LeanObject = *_args.add(7);
    let mut v_00_u03b3_1590_: *mut LeanObject = *_args.add(8);
    let mut v_Pl_1591_: *mut LeanObject = *_args.add(9);
    let mut v_LargeEnough_1592_: *mut LeanObject = *_args.add(10);
    let mut v_hl_1593_: *mut LeanObject = *_args.add(11);
    let mut v_upperBound_1594_: *mut LeanObject = *_args.add(12);
    let mut v_acc_1595_: *mut LeanObject = *_args.add(13);
    let mut v_next_1596_: *mut LeanObject = *_args.add(14);
    let mut v_h_1597_: *mut LeanObject = *_args.add(15);
    let mut v_f_1598_: *mut LeanObject = *_args.add(16);
    let mut v_res_1599_: *mut LeanObject = core::ptr::null_mut();
    v_res_1599_ = l_Std_Rxc_Iterator_instIteratorLoop_loop(
        v_00_u03b1_1582_,
        v_inst_1583_,
        v_inst_1584_,
        v_inst_1585_,
        v_inst_1586_,
        v_inst_1587_,
        v_n_1588_,
        v_inst_1589_,
        v_00_u03b3_1590_,
        v_Pl_1591_,
        v_LargeEnough_1592_,
        v_hl_1593_,
        v_upperBound_1594_,
        v_acc_1595_,
        v_next_1596_,
        v_h_1597_,
        v_f_1598_,
    );
    return v_res_1599_;
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0(
    mut v_toPure_1600_: *mut LeanObject,
    mut v_inst_1601_: *mut LeanObject,
    mut v_next_1602_: *mut LeanObject,
    mut v_G_1603_: *mut LeanObject,
    mut v_____do__lift_1604_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1604_) == 0 {
        let mut v_a_1605_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_G_1603_);
        lean_dec(v_next_1602_);
        lean_dec_ref(v_inst_1601_);
        v_a_1605_ = lean_ctor_get(v_____do__lift_1604_, 0);
        lean_inc(v_a_1605_);
        lean_dec_ref_known(v_____do__lift_1604_, 1);
        v___x_1606_ = lean_apply_2(v_toPure_1600_, lean_box(0), v_a_1605_);
        return v___x_1606_;
    } else {
        let mut v_a_1607_: *mut LeanObject = core::ptr::null_mut();
        let mut v_succ_x3f_1608_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
        v_a_1607_ = lean_ctor_get(v_____do__lift_1604_, 0);
        lean_inc(v_a_1607_);
        lean_dec_ref_known(v_____do__lift_1604_, 1);
        v_succ_x3f_1608_ = lean_ctor_get(v_inst_1601_, 0);
        lean_inc_ref(v_succ_x3f_1608_);
        lean_dec_ref(v_inst_1601_);
        v___x_1609_ = lean_apply_1(v_succ_x3f_1608_, v_next_1602_);
        if lean_obj_tag(v___x_1609_) == 0 {
            let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_G_1603_);
            v___x_1610_ = lean_apply_2(v_toPure_1600_, lean_box(0), v_a_1607_);
            return v___x_1610_;
        } else {
            let mut v_val_1611_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toPure_1600_);
            v_val_1611_ = lean_ctor_get(v___x_1609_, 0);
            lean_inc(v_val_1611_);
            lean_dec_ref_known(v___x_1609_, 1);
            v___x_1612_ = lean_apply_4(v_G_1603_, v_val_1611_, v_a_1607_, lean_box(0), lean_box(0));
            return v___x_1612_;
        }
    }
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1(
    mut v_inst_1613_: *mut LeanObject,
    mut v_upperBound_1614_: *mut LeanObject,
    mut v_toPure_1615_: *mut LeanObject,
    mut v_inst_1616_: *mut LeanObject,
    mut v_f_1617_: *mut LeanObject,
    mut v_toBind_1618_: *mut LeanObject,
    mut v_next_1619_: *mut LeanObject,
    mut v_acc_1620_: *mut LeanObject,
    mut v_h_1621_: *mut LeanObject,
    mut v_G_1622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: u8 = 0;
    lean_inc(v_next_1619_);
    v___x_1623_ = lean_apply_2(v_inst_1613_, v_next_1619_, v_upperBound_1614_);
    v___x_1624_ = (lean_unbox(v___x_1623_) as u8);
    if v___x_1624_ == 0 {
        let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_G_1622_);
        lean_dec(v_next_1619_);
        lean_dec(v_toBind_1618_);
        lean_dec(v_f_1617_);
        lean_dec_ref(v_inst_1616_);
        v___x_1625_ = lean_apply_2(v_toPure_1615_, lean_box(0), v_acc_1620_);
        return v___x_1625_;
    } else {
        let mut v___f_1626_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_next_1619_);
        v___f_1626_ = lean_alloc_closure(
            l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1626_, 0, v_toPure_1615_);
        lean_closure_set(v___f_1626_, 1, v_inst_1616_);
        lean_closure_set(v___f_1626_, 2, v_next_1619_);
        lean_closure_set(v___f_1626_, 3, v_G_1622_);
        v___x_1627_ = lean_apply_3(v_f_1617_, v_next_1619_, lean_box(0), v_acc_1620_);
        v___x_1628_ = lean_apply_4(
            v_toBind_1618_,
            lean_box(0),
            lean_box(0),
            v___x_1627_,
            v___f_1626_,
        );
        return v___x_1628_;
    }
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2(
    mut v_toPure_1629_: *mut LeanObject,
    mut v_inst_1630_: *mut LeanObject,
    mut v_inst_1631_: *mut LeanObject,
    mut v_toBind_1632_: *mut LeanObject,
    mut v_x_1633_: *mut LeanObject,
    mut v_00_u03b3_1634_: *mut LeanObject,
    mut v_Pl_1635_: *mut LeanObject,
    mut v_it_1636_: *mut LeanObject,
    mut v_init_1637_: *mut LeanObject,
    mut v_f_1638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_1639_: *mut LeanObject = core::ptr::null_mut();
    v_next_1639_ = lean_ctor_get(v_it_1636_, 0);
    lean_inc(v_next_1639_);
    if lean_obj_tag(v_next_1639_) == 0 {
        let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_1638_);
        lean_dec_ref(v_it_1636_);
        lean_dec(v_toBind_1632_);
        lean_dec_ref(v_inst_1631_);
        lean_dec_ref(v_inst_1630_);
        v___x_1640_ = lean_apply_2(v_toPure_1629_, lean_box(0), v_init_1637_);
        return v___x_1640_;
    } else {
        let mut v_upperBound_1641_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_1642_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1643_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
        v_upperBound_1641_ = lean_ctor_get(v_it_1636_, 1);
        lean_inc(v_upperBound_1641_);
        lean_dec_ref(v_it_1636_);
        v_val_1642_ = lean_ctor_get(v_next_1639_, 0);
        lean_inc(v_val_1642_);
        lean_dec_ref_known(v_next_1639_, 1);
        v___f_1643_ = lean_alloc_closure(
            l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
            10,
            6,
        );
        lean_closure_set(v___f_1643_, 0, v_inst_1630_);
        lean_closure_set(v___f_1643_, 1, v_upperBound_1641_);
        lean_closure_set(v___f_1643_, 2, v_toPure_1629_);
        lean_closure_set(v___f_1643_, 3, v_inst_1631_);
        lean_closure_set(v___f_1643_, 4, v_f_1638_);
        lean_closure_set(v___f_1643_, 5, v_toBind_1632_);
        v___x_1644_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_1643_,
            v_val_1642_,
            v_init_1637_,
            lean_box(0),
        );
        return v___x_1644_;
    }
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2___boxed(
    mut v_toPure_1645_: *mut LeanObject,
    mut v_inst_1646_: *mut LeanObject,
    mut v_inst_1647_: *mut LeanObject,
    mut v_toBind_1648_: *mut LeanObject,
    mut v_x_1649_: *mut LeanObject,
    mut v_00_u03b3_1650_: *mut LeanObject,
    mut v_Pl_1651_: *mut LeanObject,
    mut v_it_1652_: *mut LeanObject,
    mut v_init_1653_: *mut LeanObject,
    mut v_f_1654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1655_: *mut LeanObject = core::ptr::null_mut();
    v_res_1655_ = l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2(
        v_toPure_1645_,
        v_inst_1646_,
        v_inst_1647_,
        v_toBind_1648_,
        v_x_1649_,
        v_00_u03b3_1650_,
        v_Pl_1651_,
        v_it_1652_,
        v_init_1653_,
        v_f_1654_,
    );
    lean_dec(v_x_1649_);
    return v_res_1655_;
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop___redArg(
    mut v_inst_1656_: *mut LeanObject,
    mut v_inst_1657_: *mut LeanObject,
    mut v_inst_1658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1662_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1659_ = lean_ctor_get(v_inst_1658_, 0);
    lean_inc_ref(v_toApplicative_1659_);
    v_toBind_1660_ = lean_ctor_get(v_inst_1658_, 1);
    lean_inc(v_toBind_1660_);
    lean_dec_ref(v_inst_1658_);
    v_toPure_1661_ = lean_ctor_get(v_toApplicative_1659_, 1);
    lean_inc(v_toPure_1661_);
    lean_dec_ref(v_toApplicative_1659_);
    v___f_1662_ = lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2___boxed as *mut core::ffi::c_void,
        10,
        4,
    );
    lean_closure_set(v___f_1662_, 0, v_toPure_1661_);
    lean_closure_set(v___f_1662_, 1, v_inst_1657_);
    lean_closure_set(v___f_1662_, 2, v_inst_1656_);
    lean_closure_set(v___f_1662_, 3, v_toBind_1660_);
    return v___f_1662_;
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop(
    mut v_00_u03b1_1663_: *mut LeanObject,
    mut v_inst_1664_: *mut LeanObject,
    mut v_inst_1665_: *mut LeanObject,
    mut v_inst_1666_: *mut LeanObject,
    mut v_inst_1667_: *mut LeanObject,
    mut v_inst_1668_: *mut LeanObject,
    mut v_n_1669_: *mut LeanObject,
    mut v_inst_1670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1674_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1671_ = lean_ctor_get(v_inst_1670_, 0);
    lean_inc_ref(v_toApplicative_1671_);
    v_toBind_1672_ = lean_ctor_get(v_inst_1670_, 1);
    lean_inc(v_toBind_1672_);
    lean_dec_ref(v_inst_1670_);
    v_toPure_1673_ = lean_ctor_get(v_toApplicative_1671_, 1);
    lean_inc(v_toPure_1673_);
    lean_dec_ref(v_toApplicative_1671_);
    v___f_1674_ = lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2___boxed as *mut core::ffi::c_void,
        10,
        4,
    );
    lean_closure_set(v___f_1674_, 0, v_toPure_1673_);
    lean_closure_set(v___f_1674_, 1, v_inst_1666_);
    lean_closure_set(v___f_1674_, 2, v_inst_1664_);
    lean_closure_set(v___f_1674_, 3, v_toBind_1672_);
    return v___f_1674_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter___redArg(
    mut v_____do__lift_1675_: *mut LeanObject,
    mut v_h__1_1676_: *mut LeanObject,
    mut v_h__2_1677_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1675_) == 0 {
        let mut v_a_1678_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1676_);
        v_a_1678_ = lean_ctor_get(v_____do__lift_1675_, 0);
        lean_inc(v_a_1678_);
        lean_dec_ref_known(v_____do__lift_1675_, 1);
        v___x_1679_ = lean_apply_2(v_h__2_1677_, v_a_1678_, lean_box(0));
        return v___x_1679_;
    } else {
        let mut v_a_1680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1677_);
        v_a_1680_ = lean_ctor_get(v_____do__lift_1675_, 0);
        lean_inc(v_a_1680_);
        lean_dec_ref_known(v_____do__lift_1675_, 1);
        v___x_1681_ = lean_apply_2(v_h__1_1676_, v_a_1680_, lean_box(0));
        return v___x_1681_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter(
    mut v_00_u03b1_1682_: *mut LeanObject,
    mut v_00_u03b3_1683_: *mut LeanObject,
    mut v_Pl_1684_: *mut LeanObject,
    mut v_acc_1685_: *mut LeanObject,
    mut v_next_1686_: *mut LeanObject,
    mut v_motive_1687_: *mut LeanObject,
    mut v_____do__lift_1688_: *mut LeanObject,
    mut v_h__1_1689_: *mut LeanObject,
    mut v_h__2_1690_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1688_) == 0 {
        let mut v_a_1691_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1689_);
        v_a_1691_ = lean_ctor_get(v_____do__lift_1688_, 0);
        lean_inc(v_a_1691_);
        lean_dec_ref_known(v_____do__lift_1688_, 1);
        v___x_1692_ = lean_apply_2(v_h__2_1690_, v_a_1691_, lean_box(0));
        return v___x_1692_;
    } else {
        let mut v_a_1693_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1690_);
        v_a_1693_ = lean_ctor_get(v_____do__lift_1688_, 0);
        lean_inc(v_a_1693_);
        lean_dec_ref_known(v_____do__lift_1688_, 1);
        v___x_1694_ = lean_apply_2(v_h__1_1689_, v_a_1693_, lean_box(0));
        return v___x_1694_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter___boxed(
    mut v_00_u03b1_1695_: *mut LeanObject,
    mut v_00_u03b3_1696_: *mut LeanObject,
    mut v_Pl_1697_: *mut LeanObject,
    mut v_acc_1698_: *mut LeanObject,
    mut v_next_1699_: *mut LeanObject,
    mut v_motive_1700_: *mut LeanObject,
    mut v_____do__lift_1701_: *mut LeanObject,
    mut v_h__1_1702_: *mut LeanObject,
    mut v_h__2_1703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1704_: *mut LeanObject = core::ptr::null_mut();
    v_res_1704_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter(v_00_u03b1_1695_, v_00_u03b3_1696_, v_Pl_1697_, v_acc_1698_, v_next_1699_, v_motive_1700_, v_____do__lift_1701_, v_h__1_1702_, v_h__2_1703_);
    lean_dec(v_next_1699_);
    lean_dec(v_acc_1698_);
    return v_res_1704_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter___redArg(
    mut v_x_1705_: *mut LeanObject,
    mut v_h__1_1706_: *mut LeanObject,
    mut v_h__2_1707_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1705_) == 0 {
        let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1706_);
        v___x_1708_ = lean_apply_1(v_h__2_1707_, lean_box(0));
        return v___x_1708_;
    } else {
        let mut v_val_1709_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1707_);
        v_val_1709_ = lean_ctor_get(v_x_1705_, 0);
        lean_inc(v_val_1709_);
        lean_dec_ref_known(v_x_1705_, 1);
        v___x_1710_ = lean_apply_2(v_h__1_1706_, v_val_1709_, lean_box(0));
        return v___x_1710_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter(
    mut v_00_u03b1_1711_: *mut LeanObject,
    mut v_motive_1712_: *mut LeanObject,
    mut v_x_1713_: *mut LeanObject,
    mut v_h__1_1714_: *mut LeanObject,
    mut v_h__2_1715_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1713_) == 0 {
        let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1714_);
        v___x_1716_ = lean_apply_1(v_h__2_1715_, lean_box(0));
        return v___x_1716_;
    } else {
        let mut v_val_1717_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1715_);
        v_val_1717_ = lean_ctor_get(v_x_1713_, 0);
        lean_inc(v_val_1717_);
        lean_dec_ref_known(v_x_1713_, 1);
        v___x_1718_ = lean_apply_2(v_h__1_1714_, v_val_1717_, lean_box(0));
        return v___x_1718_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___redArg(
    mut v_____do__lift_1719_: *mut LeanObject,
    mut v_h__1_1720_: *mut LeanObject,
    mut v_h__2_1721_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1719_) == 0 {
        let mut v_a_1722_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1720_);
        v_a_1722_ = lean_ctor_get(v_____do__lift_1719_, 0);
        lean_inc(v_a_1722_);
        lean_dec_ref_known(v_____do__lift_1719_, 1);
        v___x_1723_ = lean_apply_2(v_h__2_1721_, v_a_1722_, lean_box(0));
        return v___x_1723_;
    } else {
        let mut v_a_1724_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1721_);
        v_a_1724_ = lean_ctor_get(v_____do__lift_1719_, 0);
        lean_inc(v_a_1724_);
        lean_dec_ref_known(v_____do__lift_1719_, 1);
        v___x_1725_ = lean_apply_2(v_h__1_1720_, v_a_1724_, lean_box(0));
        return v___x_1725_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter(
    mut v_00_u03b1_1726_: *mut LeanObject,
    mut v_00_u03b3_1727_: *mut LeanObject,
    mut v_Pl_1728_: *mut LeanObject,
    mut v_next_1729_: *mut LeanObject,
    mut v_acc_1730_: *mut LeanObject,
    mut v_motive_1731_: *mut LeanObject,
    mut v_____do__lift_1732_: *mut LeanObject,
    mut v_h__1_1733_: *mut LeanObject,
    mut v_h__2_1734_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1732_) == 0 {
        let mut v_a_1735_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1733_);
        v_a_1735_ = lean_ctor_get(v_____do__lift_1732_, 0);
        lean_inc(v_a_1735_);
        lean_dec_ref_known(v_____do__lift_1732_, 1);
        v___x_1736_ = lean_apply_2(v_h__2_1734_, v_a_1735_, lean_box(0));
        return v___x_1736_;
    } else {
        let mut v_a_1737_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1734_);
        v_a_1737_ = lean_ctor_get(v_____do__lift_1732_, 0);
        lean_inc(v_a_1737_);
        lean_dec_ref_known(v_____do__lift_1732_, 1);
        v___x_1738_ = lean_apply_2(v_h__1_1733_, v_a_1737_, lean_box(0));
        return v___x_1738_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___boxed(
    mut v_00_u03b1_1739_: *mut LeanObject,
    mut v_00_u03b3_1740_: *mut LeanObject,
    mut v_Pl_1741_: *mut LeanObject,
    mut v_next_1742_: *mut LeanObject,
    mut v_acc_1743_: *mut LeanObject,
    mut v_motive_1744_: *mut LeanObject,
    mut v_____do__lift_1745_: *mut LeanObject,
    mut v_h__1_1746_: *mut LeanObject,
    mut v_h__2_1747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1748_: *mut LeanObject = core::ptr::null_mut();
    v_res_1748_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter(v_00_u03b1_1739_, v_00_u03b3_1740_, v_Pl_1741_, v_next_1742_, v_acc_1743_, v_motive_1744_, v_____do__lift_1745_, v_h__1_1746_, v_h__2_1747_);
    lean_dec(v_acc_1743_);
    lean_dec(v_next_1742_);
    return v_res_1748_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_1749_: *mut LeanObject,
    mut v_h__1_1750_: *mut LeanObject,
    mut v_h__2_1751_: *mut LeanObject,
    mut v_h__3_1752_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1749_) {
        0 => {
            let mut v_it_1753_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_1754_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1752_);
            lean_dec(v_h__2_1751_);
            v_it_1753_ = lean_ctor_get(v_x_1749_, 0);
            lean_inc(v_it_1753_);
            v_out_1754_ = lean_ctor_get(v_x_1749_, 1);
            lean_inc(v_out_1754_);
            lean_dec_ref_known(v_x_1749_, 2);
            v___x_1755_ = lean_apply_3(v_h__1_1750_, v_it_1753_, v_out_1754_, lean_box(0));
            return v___x_1755_;
        }
        1 => {
            let mut v_it_1756_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1752_);
            lean_dec(v_h__1_1750_);
            v_it_1756_ = lean_ctor_get(v_x_1749_, 0);
            lean_inc(v_it_1756_);
            lean_dec_ref_known(v_x_1749_, 1);
            v___x_1757_ = lean_apply_2(v_h__2_1751_, v_it_1756_, lean_box(0));
            return v___x_1757_;
        }
        _ => {
            let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1751_);
            lean_dec(v_h__1_1750_);
            v___x_1758_ = lean_apply_1(v_h__3_1752_, lean_box(0));
            return v___x_1758_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_1759_: *mut LeanObject,
    mut v_00_u03b2_1760_: *mut LeanObject,
    mut v_m_1761_: *mut LeanObject,
    mut v_inst_1762_: *mut LeanObject,
    mut v_it_1763_: *mut LeanObject,
    mut v_motive_1764_: *mut LeanObject,
    mut v_x_1765_: *mut LeanObject,
    mut v_h__1_1766_: *mut LeanObject,
    mut v_h__2_1767_: *mut LeanObject,
    mut v_h__3_1768_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1765_) {
        0 => {
            let mut v_it_1769_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_1770_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1768_);
            lean_dec(v_h__2_1767_);
            v_it_1769_ = lean_ctor_get(v_x_1765_, 0);
            lean_inc(v_it_1769_);
            v_out_1770_ = lean_ctor_get(v_x_1765_, 1);
            lean_inc(v_out_1770_);
            lean_dec_ref_known(v_x_1765_, 2);
            v___x_1771_ = lean_apply_3(v_h__1_1766_, v_it_1769_, v_out_1770_, lean_box(0));
            return v___x_1771_;
        }
        1 => {
            let mut v_it_1772_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1768_);
            lean_dec(v_h__1_1766_);
            v_it_1772_ = lean_ctor_get(v_x_1765_, 0);
            lean_inc(v_it_1772_);
            lean_dec_ref_known(v_x_1765_, 1);
            v___x_1773_ = lean_apply_2(v_h__2_1767_, v_it_1772_, lean_box(0));
            return v___x_1773_;
        }
        _ => {
            let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1767_);
            lean_dec(v_h__1_1766_);
            v___x_1774_ = lean_apply_1(v_h__3_1768_, lean_box(0));
            return v___x_1774_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_1775_: *mut LeanObject,
    mut v_00_u03b2_1776_: *mut LeanObject,
    mut v_m_1777_: *mut LeanObject,
    mut v_inst_1778_: *mut LeanObject,
    mut v_it_1779_: *mut LeanObject,
    mut v_motive_1780_: *mut LeanObject,
    mut v_x_1781_: *mut LeanObject,
    mut v_h__1_1782_: *mut LeanObject,
    mut v_h__2_1783_: *mut LeanObject,
    mut v_h__3_1784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1785_: *mut LeanObject = core::ptr::null_mut();
    v_res_1785_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_1775_, v_00_u03b2_1776_, v_m_1777_, v_inst_1778_, v_it_1779_, v_motive_1780_, v_x_1781_, v_h__1_1782_, v_h__2_1783_, v_h__3_1784_);
    lean_dec(v_it_1779_);
    lean_dec(v_inst_1778_);
    return v_res_1785_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_1786_: *mut LeanObject,
    mut v_h__1_1787_: *mut LeanObject,
    mut v_h__2_1788_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1786_) == 0 {
        let mut v_a_1789_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1787_);
        v_a_1789_ = lean_ctor_get(v_____do__lift_1786_, 0);
        lean_inc(v_a_1789_);
        lean_dec_ref_known(v_____do__lift_1786_, 1);
        v___x_1790_ = lean_apply_2(v_h__2_1788_, v_a_1789_, lean_box(0));
        return v___x_1790_;
    } else {
        let mut v_a_1791_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1788_);
        v_a_1791_ = lean_ctor_get(v_____do__lift_1786_, 0);
        lean_inc(v_a_1791_);
        lean_dec_ref_known(v_____do__lift_1786_, 1);
        v___x_1792_ = lean_apply_2(v_h__1_1787_, v_a_1791_, lean_box(0));
        return v___x_1792_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b2_1793_: *mut LeanObject,
    mut v_00_u03b3_1794_: *mut LeanObject,
    mut v_init_1795_: *mut LeanObject,
    mut v_PlausibleForInStep_1796_: *mut LeanObject,
    mut v_out_1797_: *mut LeanObject,
    mut v_motive_1798_: *mut LeanObject,
    mut v_____do__lift_1799_: *mut LeanObject,
    mut v_h__1_1800_: *mut LeanObject,
    mut v_h__2_1801_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1799_) == 0 {
        let mut v_a_1802_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1800_);
        v_a_1802_ = lean_ctor_get(v_____do__lift_1799_, 0);
        lean_inc(v_a_1802_);
        lean_dec_ref_known(v_____do__lift_1799_, 1);
        v___x_1803_ = lean_apply_2(v_h__2_1801_, v_a_1802_, lean_box(0));
        return v___x_1803_;
    } else {
        let mut v_a_1804_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1801_);
        v_a_1804_ = lean_ctor_get(v_____do__lift_1799_, 0);
        lean_inc(v_a_1804_);
        lean_dec_ref_known(v_____do__lift_1799_, 1);
        v___x_1805_ = lean_apply_2(v_h__1_1800_, v_a_1804_, lean_box(0));
        return v___x_1805_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___boxed(
    mut v_00_u03b2_1806_: *mut LeanObject,
    mut v_00_u03b3_1807_: *mut LeanObject,
    mut v_init_1808_: *mut LeanObject,
    mut v_PlausibleForInStep_1809_: *mut LeanObject,
    mut v_out_1810_: *mut LeanObject,
    mut v_motive_1811_: *mut LeanObject,
    mut v_____do__lift_1812_: *mut LeanObject,
    mut v_h__1_1813_: *mut LeanObject,
    mut v_h__2_1814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1815_: *mut LeanObject = core::ptr::null_mut();
    v_res_1815_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(v_00_u03b2_1806_, v_00_u03b3_1807_, v_init_1808_, v_PlausibleForInStep_1809_, v_out_1810_, v_motive_1811_, v_____do__lift_1812_, v_h__1_1813_, v_h__2_1814_);
    lean_dec(v_out_1810_);
    lean_dec(v_init_1808_);
    return v_res_1815_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___redArg(
    mut v_it_1816_: *mut LeanObject,
    mut v_f_1817_: *mut LeanObject,
    mut v_h__1_1818_: *mut LeanObject,
    mut v_h__2_1819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_1820_: *mut LeanObject = core::ptr::null_mut();
    v_next_1820_ = lean_ctor_get(v_it_1816_, 0);
    if lean_obj_tag(v_next_1820_) == 0 {
        let mut v_upperBound_1821_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1818_);
        v_upperBound_1821_ = lean_ctor_get(v_it_1816_, 1);
        lean_inc(v_upperBound_1821_);
        lean_dec_ref(v_it_1816_);
        v___x_1822_ = lean_apply_2(v_h__2_1819_, v_upperBound_1821_, v_f_1817_);
        return v___x_1822_;
    } else {
        let mut v_upperBound_1823_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_1824_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_next_1820_);
        lean_dec(v_h__2_1819_);
        v_upperBound_1823_ = lean_ctor_get(v_it_1816_, 1);
        lean_inc(v_upperBound_1823_);
        lean_dec_ref(v_it_1816_);
        v_val_1824_ = lean_ctor_get(v_next_1820_, 0);
        lean_inc(v_val_1824_);
        lean_dec_ref_known(v_next_1820_, 1);
        v___x_1825_ = lean_apply_3(v_h__1_1818_, v_val_1824_, v_upperBound_1823_, v_f_1817_);
        return v___x_1825_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter(
    mut v_00_u03b1_1826_: *mut LeanObject,
    mut v_inst_1827_: *mut LeanObject,
    mut v_inst_1828_: *mut LeanObject,
    mut v_inst_1829_: *mut LeanObject,
    mut v_n_1830_: *mut LeanObject,
    mut v_00_u03b3_1831_: *mut LeanObject,
    mut v_Pl_1832_: *mut LeanObject,
    mut v_motive_1833_: *mut LeanObject,
    mut v_it_1834_: *mut LeanObject,
    mut v_f_1835_: *mut LeanObject,
    mut v_h__1_1836_: *mut LeanObject,
    mut v_h__2_1837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_1838_: *mut LeanObject = core::ptr::null_mut();
    v_next_1838_ = lean_ctor_get(v_it_1834_, 0);
    if lean_obj_tag(v_next_1838_) == 0 {
        let mut v_upperBound_1839_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1836_);
        v_upperBound_1839_ = lean_ctor_get(v_it_1834_, 1);
        lean_inc(v_upperBound_1839_);
        lean_dec_ref(v_it_1834_);
        v___x_1840_ = lean_apply_2(v_h__2_1837_, v_upperBound_1839_, v_f_1835_);
        return v___x_1840_;
    } else {
        let mut v_upperBound_1841_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_1842_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_next_1838_);
        lean_dec(v_h__2_1837_);
        v_upperBound_1841_ = lean_ctor_get(v_it_1834_, 1);
        lean_inc(v_upperBound_1841_);
        lean_dec_ref(v_it_1834_);
        v_val_1842_ = lean_ctor_get(v_next_1838_, 0);
        lean_inc(v_val_1842_);
        lean_dec_ref_known(v_next_1838_, 1);
        v___x_1843_ = lean_apply_3(v_h__1_1836_, v_val_1842_, v_upperBound_1841_, v_f_1835_);
        return v___x_1843_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___boxed(
    mut v_00_u03b1_1844_: *mut LeanObject,
    mut v_inst_1845_: *mut LeanObject,
    mut v_inst_1846_: *mut LeanObject,
    mut v_inst_1847_: *mut LeanObject,
    mut v_n_1848_: *mut LeanObject,
    mut v_00_u03b3_1849_: *mut LeanObject,
    mut v_Pl_1850_: *mut LeanObject,
    mut v_motive_1851_: *mut LeanObject,
    mut v_it_1852_: *mut LeanObject,
    mut v_f_1853_: *mut LeanObject,
    mut v_h__1_1854_: *mut LeanObject,
    mut v_h__2_1855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1856_: *mut LeanObject = core::ptr::null_mut();
    v_res_1856_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_1844_, v_inst_1845_, v_inst_1846_, v_inst_1847_, v_n_1848_, v_00_u03b3_1849_, v_Pl_1850_, v_motive_1851_, v_it_1852_, v_f_1853_, v_h__1_1854_, v_h__2_1855_);
    lean_dec_ref(v_inst_1847_);
    lean_dec_ref(v_inst_1845_);
    return v_res_1856_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(
    mut v_x_1857_: *mut LeanObject,
    mut v_h__1_1858_: *mut LeanObject,
    mut v_h__2_1859_: *mut LeanObject,
    mut v_h__3_1860_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1857_) {
        0 => {
            let mut v_it_1861_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_1862_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1860_);
            lean_dec(v_h__2_1859_);
            v_it_1861_ = lean_ctor_get(v_x_1857_, 0);
            lean_inc(v_it_1861_);
            v_out_1862_ = lean_ctor_get(v_x_1857_, 1);
            lean_inc(v_out_1862_);
            lean_dec_ref_known(v_x_1857_, 2);
            v___x_1863_ = lean_apply_3(v_h__1_1858_, v_it_1861_, v_out_1862_, lean_box(0));
            return v___x_1863_;
        }
        1 => {
            let mut v_it_1864_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1860_);
            lean_dec(v_h__1_1858_);
            v_it_1864_ = lean_ctor_get(v_x_1857_, 0);
            lean_inc(v_it_1864_);
            lean_dec_ref_known(v_x_1857_, 1);
            v___x_1865_ = lean_apply_2(v_h__2_1859_, v_it_1864_, lean_box(0));
            return v___x_1865_;
        }
        _ => {
            let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1859_);
            lean_dec(v_h__1_1858_);
            v___x_1866_ = lean_apply_1(v_h__3_1860_, lean_box(0));
            return v___x_1866_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(
    mut v_m_1867_: *mut LeanObject,
    mut v_00_u03b1_1868_: *mut LeanObject,
    mut v_00_u03b2_1869_: *mut LeanObject,
    mut v_inst_1870_: *mut LeanObject,
    mut v_it_1871_: *mut LeanObject,
    mut v_motive_1872_: *mut LeanObject,
    mut v_x_1873_: *mut LeanObject,
    mut v_h__1_1874_: *mut LeanObject,
    mut v_h__2_1875_: *mut LeanObject,
    mut v_h__3_1876_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1873_) {
        0 => {
            let mut v_it_1877_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_1878_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1876_);
            lean_dec(v_h__2_1875_);
            v_it_1877_ = lean_ctor_get(v_x_1873_, 0);
            lean_inc(v_it_1877_);
            v_out_1878_ = lean_ctor_get(v_x_1873_, 1);
            lean_inc(v_out_1878_);
            lean_dec_ref_known(v_x_1873_, 2);
            v___x_1879_ = lean_apply_3(v_h__1_1874_, v_it_1877_, v_out_1878_, lean_box(0));
            return v___x_1879_;
        }
        1 => {
            let mut v_it_1880_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1876_);
            lean_dec(v_h__1_1874_);
            v_it_1880_ = lean_ctor_get(v_x_1873_, 0);
            lean_inc(v_it_1880_);
            lean_dec_ref_known(v_x_1873_, 1);
            v___x_1881_ = lean_apply_2(v_h__2_1875_, v_it_1880_, lean_box(0));
            return v___x_1881_;
        }
        _ => {
            let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1875_);
            lean_dec(v_h__1_1874_);
            v___x_1882_ = lean_apply_1(v_h__3_1876_, lean_box(0));
            return v___x_1882_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(
    mut v_m_1883_: *mut LeanObject,
    mut v_00_u03b1_1884_: *mut LeanObject,
    mut v_00_u03b2_1885_: *mut LeanObject,
    mut v_inst_1886_: *mut LeanObject,
    mut v_it_1887_: *mut LeanObject,
    mut v_motive_1888_: *mut LeanObject,
    mut v_x_1889_: *mut LeanObject,
    mut v_h__1_1890_: *mut LeanObject,
    mut v_h__2_1891_: *mut LeanObject,
    mut v_h__3_1892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1893_: *mut LeanObject = core::ptr::null_mut();
    v_res_1893_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(v_m_1883_, v_00_u03b1_1884_, v_00_u03b2_1885_, v_inst_1886_, v_it_1887_, v_motive_1888_, v_x_1889_, v_h__1_1890_, v_h__2_1891_, v_h__3_1892_);
    lean_dec(v_it_1887_);
    lean_dec(v_inst_1886_);
    return v_res_1893_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(
    mut v_____do__lift_1894_: *mut LeanObject,
    mut v_h__1_1895_: *mut LeanObject,
    mut v_h__2_1896_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1894_) == 0 {
        let mut v_a_1897_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1895_);
        v_a_1897_ = lean_ctor_get(v_____do__lift_1894_, 0);
        lean_inc(v_a_1897_);
        lean_dec_ref_known(v_____do__lift_1894_, 1);
        v___x_1898_ = lean_apply_2(v_h__2_1896_, v_a_1897_, lean_box(0));
        return v___x_1898_;
    } else {
        let mut v_a_1899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1896_);
        v_a_1899_ = lean_ctor_get(v_____do__lift_1894_, 0);
        lean_inc(v_a_1899_);
        lean_dec_ref_known(v_____do__lift_1894_, 1);
        v___x_1900_ = lean_apply_2(v_h__1_1895_, v_a_1899_, lean_box(0));
        return v___x_1900_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(
    mut v_00_u03b2_1901_: *mut LeanObject,
    mut v_00_u03b3_1902_: *mut LeanObject,
    mut v_PlausibleForInStep_1903_: *mut LeanObject,
    mut v_acc_1904_: *mut LeanObject,
    mut v_out_1905_: *mut LeanObject,
    mut v_motive_1906_: *mut LeanObject,
    mut v_____do__lift_1907_: *mut LeanObject,
    mut v_h__1_1908_: *mut LeanObject,
    mut v_h__2_1909_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1907_) == 0 {
        let mut v_a_1910_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1908_);
        v_a_1910_ = lean_ctor_get(v_____do__lift_1907_, 0);
        lean_inc(v_a_1910_);
        lean_dec_ref_known(v_____do__lift_1907_, 1);
        v___x_1911_ = lean_apply_2(v_h__2_1909_, v_a_1910_, lean_box(0));
        return v___x_1911_;
    } else {
        let mut v_a_1912_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1909_);
        v_a_1912_ = lean_ctor_get(v_____do__lift_1907_, 0);
        lean_inc(v_a_1912_);
        lean_dec_ref_known(v_____do__lift_1907_, 1);
        v___x_1913_ = lean_apply_2(v_h__1_1908_, v_a_1912_, lean_box(0));
        return v___x_1913_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(
    mut v_00_u03b2_1914_: *mut LeanObject,
    mut v_00_u03b3_1915_: *mut LeanObject,
    mut v_PlausibleForInStep_1916_: *mut LeanObject,
    mut v_acc_1917_: *mut LeanObject,
    mut v_out_1918_: *mut LeanObject,
    mut v_motive_1919_: *mut LeanObject,
    mut v_____do__lift_1920_: *mut LeanObject,
    mut v_h__1_1921_: *mut LeanObject,
    mut v_h__2_1922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1923_: *mut LeanObject = core::ptr::null_mut();
    v_res_1923_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(v_00_u03b2_1914_, v_00_u03b3_1915_, v_PlausibleForInStep_1916_, v_acc_1917_, v_out_1918_, v_motive_1919_, v_____do__lift_1920_, v_h__1_1921_, v_h__2_1922_);
    lean_dec(v_out_1918_);
    lean_dec(v_acc_1917_);
    return v_res_1923_;
}
pub unsafe fn l_Std_Rxo_Iterator_Monadic_step___redArg(
    mut v_inst_1924_: *mut LeanObject,
    mut v_inst_1925_: *mut LeanObject,
    mut v_it_1926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1932_: u8 = 0;
    let mut v_val_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1940_: u8 = 0;
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1948_: u8 = 0;
    let mut v_unused_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1950_: u8 = 0;
    let mut v_unused_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1927_ = lean_ctor_get(v_it_1926_, 0);
                lean_inc(v_next_1927_);
                if lean_obj_tag(v_next_1927_) == 0 {
                    lean_dec_ref(v_it_1926_);
                    lean_dec_ref(v_inst_1925_);
                    lean_dec_ref(v_inst_1924_);
                    v___x_1928_ = lean_box(2);
                    return v___x_1928_;
                } else {
                    v_upperBound_1929_ = lean_ctor_get(v_it_1926_, 1);
                    v_isSharedCheck_1950_ = (!lean_is_exclusive(v_it_1926_)) as u8;
                    if v_isSharedCheck_1950_ == 0 {
                        v_unused_1951_ = lean_ctor_get(v_it_1926_, 0);
                        lean_dec(v_unused_1951_);
                        v___x_1931_ = v_it_1926_;
                        v_isShared_1932_ = v_isSharedCheck_1950_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_upperBound_1929_);
                        lean_dec(v_it_1926_);
                        v___x_1931_ = lean_box(0);
                        v_isShared_1932_ = v_isSharedCheck_1950_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1933_ = lean_ctor_get(v_next_1927_, 0);
                lean_inc_n(v_val_1933_, 2);
                lean_dec_ref_known(v_next_1927_, 1);
                lean_inc(v_upperBound_1929_);
                v___x_1934_ = lean_apply_2(v_inst_1925_, v_val_1933_, v_upperBound_1929_);
                v___x_1935_ = (lean_unbox(v___x_1934_) as u8);
                if v___x_1935_ == 0 {
                    lean_dec(v_val_1933_);
                    lean_del_object(v___x_1931_);
                    lean_dec(v_upperBound_1929_);
                    lean_dec_ref(v_inst_1924_);
                    v___x_1936_ = lean_box(2);
                    return v___x_1936_;
                } else {
                    v_succ_x3f_1937_ = lean_ctor_get(v_inst_1924_, 0);
                    v_isSharedCheck_1948_ = (!lean_is_exclusive(v_inst_1924_)) as u8;
                    if v_isSharedCheck_1948_ == 0 {
                        v_unused_1949_ = lean_ctor_get(v_inst_1924_, 1);
                        lean_dec(v_unused_1949_);
                        v___x_1939_ = v_inst_1924_;
                        v_isShared_1940_ = v_isSharedCheck_1948_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_succ_x3f_1937_);
                        lean_dec(v_inst_1924_);
                        v___x_1939_ = lean_box(0);
                        v_isShared_1940_ = v_isSharedCheck_1948_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                lean_inc(v_val_1933_);
                v___x_1941_ = lean_apply_1(v_succ_x3f_1937_, v_val_1933_);
                if v_isShared_1932_ == 0 {
                    lean_ctor_set(v___x_1931_, 0, v___x_1941_);
                    v___x_1943_ = v___x_1931_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1941_);
                    lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_upperBound_1929_);
                    v___x_1943_ = v_reuseFailAlloc_1947_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1940_ == 0 {
                    lean_ctor_set(v___x_1939_, 1, v_val_1933_);
                    lean_ctor_set(v___x_1939_, 0, v___x_1943_);
                    v___x_1945_ = v___x_1939_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
                    lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_val_1933_);
                    v___x_1945_ = v_reuseFailAlloc_1946_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1945_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxo_Iterator_Monadic_step(
    mut v_00_u03b1_1952_: *mut LeanObject,
    mut v_inst_1953_: *mut LeanObject,
    mut v_inst_1954_: *mut LeanObject,
    mut v_inst_1955_: *mut LeanObject,
    mut v_it_1956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1962_: u8 = 0;
    let mut v_val_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1970_: u8 = 0;
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1978_: u8 = 0;
    let mut v_unused_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1980_: u8 = 0;
    let mut v_unused_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1957_ = lean_ctor_get(v_it_1956_, 0);
                lean_inc(v_next_1957_);
                if lean_obj_tag(v_next_1957_) == 0 {
                    lean_dec_ref(v_it_1956_);
                    lean_dec_ref(v_inst_1955_);
                    lean_dec_ref(v_inst_1953_);
                    v___x_1958_ = lean_box(2);
                    return v___x_1958_;
                } else {
                    v_upperBound_1959_ = lean_ctor_get(v_it_1956_, 1);
                    v_isSharedCheck_1980_ = (!lean_is_exclusive(v_it_1956_)) as u8;
                    if v_isSharedCheck_1980_ == 0 {
                        v_unused_1981_ = lean_ctor_get(v_it_1956_, 0);
                        lean_dec(v_unused_1981_);
                        v___x_1961_ = v_it_1956_;
                        v_isShared_1962_ = v_isSharedCheck_1980_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_upperBound_1959_);
                        lean_dec(v_it_1956_);
                        v___x_1961_ = lean_box(0);
                        v_isShared_1962_ = v_isSharedCheck_1980_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1963_ = lean_ctor_get(v_next_1957_, 0);
                lean_inc_n(v_val_1963_, 2);
                lean_dec_ref_known(v_next_1957_, 1);
                lean_inc(v_upperBound_1959_);
                v___x_1964_ = lean_apply_2(v_inst_1955_, v_val_1963_, v_upperBound_1959_);
                v___x_1965_ = (lean_unbox(v___x_1964_) as u8);
                if v___x_1965_ == 0 {
                    lean_dec(v_val_1963_);
                    lean_del_object(v___x_1961_);
                    lean_dec(v_upperBound_1959_);
                    lean_dec_ref(v_inst_1953_);
                    v___x_1966_ = lean_box(2);
                    return v___x_1966_;
                } else {
                    v_succ_x3f_1967_ = lean_ctor_get(v_inst_1953_, 0);
                    v_isSharedCheck_1978_ = (!lean_is_exclusive(v_inst_1953_)) as u8;
                    if v_isSharedCheck_1978_ == 0 {
                        v_unused_1979_ = lean_ctor_get(v_inst_1953_, 1);
                        lean_dec(v_unused_1979_);
                        v___x_1969_ = v_inst_1953_;
                        v_isShared_1970_ = v_isSharedCheck_1978_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_succ_x3f_1967_);
                        lean_dec(v_inst_1953_);
                        v___x_1969_ = lean_box(0);
                        v_isShared_1970_ = v_isSharedCheck_1978_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                lean_inc(v_val_1963_);
                v___x_1971_ = lean_apply_1(v_succ_x3f_1967_, v_val_1963_);
                if v_isShared_1962_ == 0 {
                    lean_ctor_set(v___x_1961_, 0, v___x_1971_);
                    v___x_1973_ = v___x_1961_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1971_);
                    lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_upperBound_1959_);
                    v___x_1973_ = v_reuseFailAlloc_1977_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1970_ == 0 {
                    lean_ctor_set(v___x_1969_, 1, v_val_1963_);
                    lean_ctor_set(v___x_1969_, 0, v___x_1973_);
                    v___x_1975_ = v___x_1969_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1973_);
                    lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_val_1963_);
                    v___x_1975_ = v_reuseFailAlloc_1976_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxo_Iterator_step___redArg(
    mut v_inst_1982_: *mut LeanObject,
    mut v_inst_1983_: *mut LeanObject,
    mut v_it_1984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1990_: u8 = 0;
    let mut v_val_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: u8 = 0;
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1998_: u8 = 0;
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2006_: u8 = 0;
    let mut v_unused_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2008_: u8 = 0;
    let mut v_unused_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1985_ = lean_ctor_get(v_it_1984_, 0);
                lean_inc(v_next_1985_);
                if lean_obj_tag(v_next_1985_) == 0 {
                    lean_dec_ref(v_it_1984_);
                    lean_dec_ref(v_inst_1983_);
                    lean_dec_ref(v_inst_1982_);
                    v___x_1986_ = lean_box(2);
                    return v___x_1986_;
                } else {
                    v_upperBound_1987_ = lean_ctor_get(v_it_1984_, 1);
                    v_isSharedCheck_2008_ = (!lean_is_exclusive(v_it_1984_)) as u8;
                    if v_isSharedCheck_2008_ == 0 {
                        v_unused_2009_ = lean_ctor_get(v_it_1984_, 0);
                        lean_dec(v_unused_2009_);
                        v___x_1989_ = v_it_1984_;
                        v_isShared_1990_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_upperBound_1987_);
                        lean_dec(v_it_1984_);
                        v___x_1989_ = lean_box(0);
                        v_isShared_1990_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1991_ = lean_ctor_get(v_next_1985_, 0);
                lean_inc_n(v_val_1991_, 2);
                lean_dec_ref_known(v_next_1985_, 1);
                lean_inc(v_upperBound_1987_);
                v___x_1992_ = lean_apply_2(v_inst_1983_, v_val_1991_, v_upperBound_1987_);
                v___x_1993_ = (lean_unbox(v___x_1992_) as u8);
                if v___x_1993_ == 0 {
                    lean_dec(v_val_1991_);
                    lean_del_object(v___x_1989_);
                    lean_dec(v_upperBound_1987_);
                    lean_dec_ref(v_inst_1982_);
                    v___x_1994_ = lean_box(2);
                    return v___x_1994_;
                } else {
                    v_succ_x3f_1995_ = lean_ctor_get(v_inst_1982_, 0);
                    v_isSharedCheck_2006_ = (!lean_is_exclusive(v_inst_1982_)) as u8;
                    if v_isSharedCheck_2006_ == 0 {
                        v_unused_2007_ = lean_ctor_get(v_inst_1982_, 1);
                        lean_dec(v_unused_2007_);
                        v___x_1997_ = v_inst_1982_;
                        v_isShared_1998_ = v_isSharedCheck_2006_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_succ_x3f_1995_);
                        lean_dec(v_inst_1982_);
                        v___x_1997_ = lean_box(0);
                        v_isShared_1998_ = v_isSharedCheck_2006_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                lean_inc(v_val_1991_);
                v___x_1999_ = lean_apply_1(v_succ_x3f_1995_, v_val_1991_);
                if v_isShared_1990_ == 0 {
                    lean_ctor_set(v___x_1989_, 0, v___x_1999_);
                    v___x_2001_ = v___x_1989_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1999_);
                    lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_upperBound_1987_);
                    v___x_2001_ = v_reuseFailAlloc_2005_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1998_ == 0 {
                    lean_ctor_set(v___x_1997_, 1, v_val_1991_);
                    lean_ctor_set(v___x_1997_, 0, v___x_2001_);
                    v___x_2003_ = v___x_1997_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
                    lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_val_1991_);
                    v___x_2003_ = v_reuseFailAlloc_2004_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2003_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxo_Iterator_step(
    mut v_00_u03b1_2010_: *mut LeanObject,
    mut v_inst_2011_: *mut LeanObject,
    mut v_inst_2012_: *mut LeanObject,
    mut v_inst_2013_: *mut LeanObject,
    mut v_it_2014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2020_: u8 = 0;
    let mut v_val_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u8 = 0;
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2036_: u8 = 0;
    let mut v_unused_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_unused_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_2015_ = lean_ctor_get(v_it_2014_, 0);
                lean_inc(v_next_2015_);
                if lean_obj_tag(v_next_2015_) == 0 {
                    lean_dec_ref(v_it_2014_);
                    lean_dec_ref(v_inst_2013_);
                    lean_dec_ref(v_inst_2011_);
                    v___x_2016_ = lean_box(2);
                    return v___x_2016_;
                } else {
                    v_upperBound_2017_ = lean_ctor_get(v_it_2014_, 1);
                    v_isSharedCheck_2038_ = (!lean_is_exclusive(v_it_2014_)) as u8;
                    if v_isSharedCheck_2038_ == 0 {
                        v_unused_2039_ = lean_ctor_get(v_it_2014_, 0);
                        lean_dec(v_unused_2039_);
                        v___x_2019_ = v_it_2014_;
                        v_isShared_2020_ = v_isSharedCheck_2038_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_upperBound_2017_);
                        lean_dec(v_it_2014_);
                        v___x_2019_ = lean_box(0);
                        v_isShared_2020_ = v_isSharedCheck_2038_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_2021_ = lean_ctor_get(v_next_2015_, 0);
                lean_inc_n(v_val_2021_, 2);
                lean_dec_ref_known(v_next_2015_, 1);
                lean_inc(v_upperBound_2017_);
                v___x_2022_ = lean_apply_2(v_inst_2013_, v_val_2021_, v_upperBound_2017_);
                v___x_2023_ = (lean_unbox(v___x_2022_) as u8);
                if v___x_2023_ == 0 {
                    lean_dec(v_val_2021_);
                    lean_del_object(v___x_2019_);
                    lean_dec(v_upperBound_2017_);
                    lean_dec_ref(v_inst_2011_);
                    v___x_2024_ = lean_box(2);
                    return v___x_2024_;
                } else {
                    v_succ_x3f_2025_ = lean_ctor_get(v_inst_2011_, 0);
                    v_isSharedCheck_2036_ = (!lean_is_exclusive(v_inst_2011_)) as u8;
                    if v_isSharedCheck_2036_ == 0 {
                        v_unused_2037_ = lean_ctor_get(v_inst_2011_, 1);
                        lean_dec(v_unused_2037_);
                        v___x_2027_ = v_inst_2011_;
                        v_isShared_2028_ = v_isSharedCheck_2036_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_succ_x3f_2025_);
                        lean_dec(v_inst_2011_);
                        v___x_2027_ = lean_box(0);
                        v_isShared_2028_ = v_isSharedCheck_2036_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                lean_inc(v_val_2021_);
                v___x_2029_ = lean_apply_1(v_succ_x3f_2025_, v_val_2021_);
                if v_isShared_2020_ == 0 {
                    lean_ctor_set(v___x_2019_, 0, v___x_2029_);
                    v___x_2031_ = v___x_2019_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2029_);
                    lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_upperBound_2017_);
                    v___x_2031_ = v_reuseFailAlloc_2035_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2028_ == 0 {
                    lean_ctor_set(v___x_2027_, 1, v_val_2021_);
                    lean_ctor_set(v___x_2027_, 0, v___x_2031_);
                    v___x_2033_ = v___x_2027_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
                    lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_val_2021_);
                    v___x_2033_ = v_reuseFailAlloc_2034_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0(
    mut v_inst_2040_: *mut LeanObject,
    mut v_inst_2041_: *mut LeanObject,
    mut v_it_2042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v_val_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: u8 = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2056_: u8 = 0;
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2064_: u8 = 0;
    let mut v_unused_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2066_: u8 = 0;
    let mut v_unused_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_2043_ = lean_ctor_get(v_it_2042_, 0);
                lean_inc(v_next_2043_);
                if lean_obj_tag(v_next_2043_) == 0 {
                    lean_dec_ref(v_it_2042_);
                    lean_dec_ref(v_inst_2041_);
                    lean_dec_ref(v_inst_2040_);
                    v___x_2044_ = lean_box(2);
                    return v___x_2044_;
                } else {
                    v_upperBound_2045_ = lean_ctor_get(v_it_2042_, 1);
                    v_isSharedCheck_2066_ = (!lean_is_exclusive(v_it_2042_)) as u8;
                    if v_isSharedCheck_2066_ == 0 {
                        v_unused_2067_ = lean_ctor_get(v_it_2042_, 0);
                        lean_dec(v_unused_2067_);
                        v___x_2047_ = v_it_2042_;
                        v_isShared_2048_ = v_isSharedCheck_2066_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_upperBound_2045_);
                        lean_dec(v_it_2042_);
                        v___x_2047_ = lean_box(0);
                        v_isShared_2048_ = v_isSharedCheck_2066_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_2049_ = lean_ctor_get(v_next_2043_, 0);
                lean_inc_n(v_val_2049_, 2);
                lean_dec_ref_known(v_next_2043_, 1);
                lean_inc(v_upperBound_2045_);
                v___x_2050_ = lean_apply_2(v_inst_2040_, v_val_2049_, v_upperBound_2045_);
                v___x_2051_ = (lean_unbox(v___x_2050_) as u8);
                if v___x_2051_ == 0 {
                    lean_dec(v_val_2049_);
                    lean_del_object(v___x_2047_);
                    lean_dec(v_upperBound_2045_);
                    lean_dec_ref(v_inst_2041_);
                    v___x_2052_ = lean_box(2);
                    return v___x_2052_;
                } else {
                    v_succ_x3f_2053_ = lean_ctor_get(v_inst_2041_, 0);
                    v_isSharedCheck_2064_ = (!lean_is_exclusive(v_inst_2041_)) as u8;
                    if v_isSharedCheck_2064_ == 0 {
                        v_unused_2065_ = lean_ctor_get(v_inst_2041_, 1);
                        lean_dec(v_unused_2065_);
                        v___x_2055_ = v_inst_2041_;
                        v_isShared_2056_ = v_isSharedCheck_2064_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_succ_x3f_2053_);
                        lean_dec(v_inst_2041_);
                        v___x_2055_ = lean_box(0);
                        v_isShared_2056_ = v_isSharedCheck_2064_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                lean_inc(v_val_2049_);
                v___x_2057_ = lean_apply_1(v_succ_x3f_2053_, v_val_2049_);
                if v_isShared_2048_ == 0 {
                    lean_ctor_set(v___x_2047_, 0, v___x_2057_);
                    v___x_2059_ = v___x_2047_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2057_);
                    lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_upperBound_2045_);
                    v___x_2059_ = v_reuseFailAlloc_2063_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2056_ == 0 {
                    lean_ctor_set(v___x_2055_, 1, v_val_2049_);
                    lean_ctor_set(v___x_2055_, 0, v___x_2059_);
                    v___x_2061_ = v___x_2055_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
                    lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_val_2049_);
                    v___x_2061_ = v_reuseFailAlloc_2062_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg(
    mut v_inst_2068_: *mut LeanObject,
    mut v_inst_2069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2070_: *mut LeanObject = core::ptr::null_mut();
    v___f_2070_ = lean_alloc_closure(
        l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2070_, 0, v_inst_2069_);
    lean_closure_set(v___f_2070_, 1, v_inst_2068_);
    return v___f_2070_;
}
pub unsafe fn l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT(
    mut v_00_u03b1_2071_: *mut LeanObject,
    mut v_inst_2072_: *mut LeanObject,
    mut v_inst_2073_: *mut LeanObject,
    mut v_inst_2074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2075_: *mut LeanObject = core::ptr::null_mut();
    v___f_2075_ = lean_alloc_closure(
        l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2075_, 0, v_inst_2074_);
    lean_closure_set(v___f_2075_, 1, v_inst_2072_);
    return v___f_2075_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation(
    mut v_00_u03b1_2076_: *mut LeanObject,
    mut v_inst_2077_: *mut LeanObject,
    mut v_inst_2078_: *mut LeanObject,
    mut v_inst_2079_: *mut LeanObject,
    mut v_inst_2080_: *mut LeanObject,
    mut v_inst_2081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    v___x_2082_ = lean_box(0);
    return v___x_2082_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___boxed(
    mut v_00_u03b1_2083_: *mut LeanObject,
    mut v_inst_2084_: *mut LeanObject,
    mut v_inst_2085_: *mut LeanObject,
    mut v_inst_2086_: *mut LeanObject,
    mut v_inst_2087_: *mut LeanObject,
    mut v_inst_2088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2089_: *mut LeanObject = core::ptr::null_mut();
    v_res_2089_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation(v_00_u03b1_2083_, v_inst_2084_, v_inst_2085_, v_inst_2086_, v_inst_2087_, v_inst_2088_);
    lean_dec_ref(v_inst_2086_);
    lean_dec_ref(v_inst_2084_);
    return v_res_2089_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation(
    mut v_00_u03b1_2090_: *mut LeanObject,
    mut v_inst_2091_: *mut LeanObject,
    mut v_inst_2092_: *mut LeanObject,
    mut v_inst_2093_: *mut LeanObject,
    mut v_inst_2094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    v___x_2095_ = lean_box(0);
    return v___x_2095_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___boxed(
    mut v_00_u03b1_2096_: *mut LeanObject,
    mut v_inst_2097_: *mut LeanObject,
    mut v_inst_2098_: *mut LeanObject,
    mut v_inst_2099_: *mut LeanObject,
    mut v_inst_2100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2101_: *mut LeanObject = core::ptr::null_mut();
    v_res_2101_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation(v_00_u03b1_2096_, v_inst_2097_, v_inst_2098_, v_inst_2099_, v_inst_2100_);
    lean_dec_ref(v_inst_2099_);
    lean_dec_ref(v_inst_2097_);
    return v_res_2101_;
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0(
    mut v_inst_2102_: *mut LeanObject,
    mut v_inst_2103_: *mut LeanObject,
    mut v_it_2104_: *mut LeanObject,
    mut v_n_2105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upperBound_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2111_: u8 = 0;
    let mut v_succ_x3f_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succMany_x3f_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2116_: u8 = 0;
    let mut v_val_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: u8 = 0;
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2131_: u8 = 0;
    let mut v_isSharedCheck_2132_: u8 = 0;
    let mut v_unused_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_2106_ = lean_ctor_get(v_it_2104_, 0);
                lean_inc(v_next_2106_);
                if lean_obj_tag(v_next_2106_) == 0 {
                    lean_dec(v_n_2105_);
                    lean_dec_ref(v_it_2104_);
                    lean_dec_ref(v_inst_2103_);
                    lean_dec_ref(v_inst_2102_);
                    v___x_2107_ = lean_box(2);
                    return v___x_2107_;
                } else {
                    v_upperBound_2108_ = lean_ctor_get(v_it_2104_, 1);
                    v_isSharedCheck_2132_ = (!lean_is_exclusive(v_it_2104_)) as u8;
                    if v_isSharedCheck_2132_ == 0 {
                        v_unused_2133_ = lean_ctor_get(v_it_2104_, 0);
                        lean_dec(v_unused_2133_);
                        v___x_2110_ = v_it_2104_;
                        v_isShared_2111_ = v_isSharedCheck_2132_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_upperBound_2108_);
                        lean_dec(v_it_2104_);
                        v___x_2110_ = lean_box(0);
                        v_isShared_2111_ = v_isSharedCheck_2132_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_succ_x3f_2112_ = lean_ctor_get(v_inst_2102_, 0);
                v_succMany_x3f_2113_ = lean_ctor_get(v_inst_2102_, 1);
                v_isSharedCheck_2131_ = (!lean_is_exclusive(v_inst_2102_)) as u8;
                if v_isSharedCheck_2131_ == 0 {
                    v___x_2115_ = v_inst_2102_;
                    v_isShared_2116_ = v_isSharedCheck_2131_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_succMany_x3f_2113_);
                    lean_inc(v_succ_x3f_2112_);
                    lean_dec(v_inst_2102_);
                    v___x_2115_ = lean_box(0);
                    v_isShared_2116_ = v_isSharedCheck_2131_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_val_2117_ = lean_ctor_get(v_next_2106_, 0);
                lean_inc(v_val_2117_);
                lean_dec_ref_known(v_next_2106_, 1);
                v___x_2118_ = lean_apply_2(v_succMany_x3f_2113_, v_n_2105_, v_val_2117_);
                if lean_obj_tag(v___x_2118_) == 0 {
                    lean_del_object(v___x_2115_);
                    lean_dec_ref(v_succ_x3f_2112_);
                    lean_del_object(v___x_2110_);
                    lean_dec(v_upperBound_2108_);
                    lean_dec_ref(v_inst_2103_);
                    v___x_2119_ = lean_box(2);
                    return v___x_2119_;
                } else {
                    v_val_2120_ = lean_ctor_get(v___x_2118_, 0);
                    lean_inc_n(v_val_2120_, 2);
                    lean_dec_ref_known(v___x_2118_, 1);
                    lean_inc(v_upperBound_2108_);
                    v___x_2121_ = lean_apply_2(v_inst_2103_, v_val_2120_, v_upperBound_2108_);
                    v___x_2122_ = (lean_unbox(v___x_2121_) as u8);
                    if v___x_2122_ == 0 {
                        lean_dec(v_val_2120_);
                        lean_del_object(v___x_2115_);
                        lean_dec_ref(v_succ_x3f_2112_);
                        lean_del_object(v___x_2110_);
                        lean_dec(v_upperBound_2108_);
                        v___x_2123_ = lean_box(2);
                        return v___x_2123_;
                    } else {
                        lean_inc(v_val_2120_);
                        v___x_2124_ = lean_apply_1(v_succ_x3f_2112_, v_val_2120_);
                        if v_isShared_2111_ == 0 {
                            lean_ctor_set(v___x_2110_, 0, v___x_2124_);
                            v___x_2126_ = v___x_2110_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2124_);
                            lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_upperBound_2108_);
                            v___x_2126_ = v_reuseFailAlloc_2130_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_2116_ == 0 {
                    lean_ctor_set(v___x_2115_, 1, v_val_2120_);
                    lean_ctor_set(v___x_2115_, 0, v___x_2126_);
                    v___x_2128_ = v___x_2115_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
                    lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_val_2120_);
                    v___x_2128_ = v_reuseFailAlloc_2129_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorAccess___redArg(
    mut v_inst_2134_: *mut LeanObject,
    mut v_inst_2135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2136_: *mut LeanObject = core::ptr::null_mut();
    v___f_2136_ = lean_alloc_closure(
        l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2136_, 0, v_inst_2134_);
    lean_closure_set(v___f_2136_, 1, v_inst_2135_);
    return v___f_2136_;
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorAccess(
    mut v_00_u03b1_2137_: *mut LeanObject,
    mut v_inst_2138_: *mut LeanObject,
    mut v_inst_2139_: *mut LeanObject,
    mut v_inst_2140_: *mut LeanObject,
    mut v_inst_2141_: *mut LeanObject,
    mut v_inst_2142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2143_: *mut LeanObject = core::ptr::null_mut();
    v___f_2143_ = lean_alloc_closure(
        l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2143_, 0, v_inst_2138_);
    lean_closure_set(v___f_2143_, 1, v_inst_2140_);
    return v___f_2143_;
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorLoop_loop___redArg(
    mut v_inst_2144_: *mut LeanObject,
    mut v_inst_2145_: *mut LeanObject,
    mut v_inst_2146_: *mut LeanObject,
    mut v_upperBound_2147_: *mut LeanObject,
    mut v_acc_2148_: *mut LeanObject,
    mut v_next_2149_: *mut LeanObject,
    mut v_f_2150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    v___f_2151_ = lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1 as *mut core::ffi::c_void,
        9,
        5,
    );
    lean_closure_set(v___f_2151_, 0, v_inst_2145_);
    lean_closure_set(v___f_2151_, 1, v_upperBound_2147_);
    lean_closure_set(v___f_2151_, 2, v_inst_2146_);
    lean_closure_set(v___f_2151_, 3, v_inst_2144_);
    lean_closure_set(v___f_2151_, 4, v_f_2150_);
    v___x_2152_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_2151_, v_next_2149_, v_acc_2148_, lean_box(0));
    return v___x_2152_;
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorLoop_loop(
    mut v_00_u03b1_2153_: *mut LeanObject,
    mut v_inst_2154_: *mut LeanObject,
    mut v_inst_2155_: *mut LeanObject,
    mut v_inst_2156_: *mut LeanObject,
    mut v_inst_2157_: *mut LeanObject,
    mut v_n_2158_: *mut LeanObject,
    mut v_inst_2159_: *mut LeanObject,
    mut v_00_u03b3_2160_: *mut LeanObject,
    mut v_Pl_2161_: *mut LeanObject,
    mut v_LargeEnough_2162_: *mut LeanObject,
    mut v_hl_2163_: *mut LeanObject,
    mut v_upperBound_2164_: *mut LeanObject,
    mut v_acc_2165_: *mut LeanObject,
    mut v_next_2166_: *mut LeanObject,
    mut v_h_2167_: *mut LeanObject,
    mut v_f_2168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    v___f_2169_ = lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1 as *mut core::ffi::c_void,
        9,
        5,
    );
    lean_closure_set(v___f_2169_, 0, v_inst_2156_);
    lean_closure_set(v___f_2169_, 1, v_upperBound_2164_);
    lean_closure_set(v___f_2169_, 2, v_inst_2159_);
    lean_closure_set(v___f_2169_, 3, v_inst_2154_);
    lean_closure_set(v___f_2169_, 4, v_f_2168_);
    v___x_2170_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_2169_, v_next_2166_, v_acc_2165_, lean_box(0));
    return v___x_2170_;
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2(
    mut v_toPure_2171_: *mut LeanObject,
    mut v_inst_2172_: *mut LeanObject,
    mut v_inst_2173_: *mut LeanObject,
    mut v_toBind_2174_: *mut LeanObject,
    mut v_x_2175_: *mut LeanObject,
    mut v_00_u03b3_2176_: *mut LeanObject,
    mut v_Pl_2177_: *mut LeanObject,
    mut v_it_2178_: *mut LeanObject,
    mut v_init_2179_: *mut LeanObject,
    mut v_f_2180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_2181_: *mut LeanObject = core::ptr::null_mut();
    v_next_2181_ = lean_ctor_get(v_it_2178_, 0);
    lean_inc(v_next_2181_);
    if lean_obj_tag(v_next_2181_) == 0 {
        let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_2180_);
        lean_dec_ref(v_it_2178_);
        lean_dec(v_toBind_2174_);
        lean_dec_ref(v_inst_2173_);
        lean_dec_ref(v_inst_2172_);
        v___x_2182_ = lean_apply_2(v_toPure_2171_, lean_box(0), v_init_2179_);
        return v___x_2182_;
    } else {
        let mut v_upperBound_2183_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_2184_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2185_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
        v_upperBound_2183_ = lean_ctor_get(v_it_2178_, 1);
        lean_inc(v_upperBound_2183_);
        lean_dec_ref(v_it_2178_);
        v_val_2184_ = lean_ctor_get(v_next_2181_, 0);
        lean_inc(v_val_2184_);
        lean_dec_ref_known(v_next_2181_, 1);
        v___f_2185_ = lean_alloc_closure(
            l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
            10,
            6,
        );
        lean_closure_set(v___f_2185_, 0, v_inst_2172_);
        lean_closure_set(v___f_2185_, 1, v_upperBound_2183_);
        lean_closure_set(v___f_2185_, 2, v_toPure_2171_);
        lean_closure_set(v___f_2185_, 3, v_inst_2173_);
        lean_closure_set(v___f_2185_, 4, v_f_2180_);
        lean_closure_set(v___f_2185_, 5, v_toBind_2174_);
        v___x_2186_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_2185_,
            v_val_2184_,
            v_init_2179_,
            lean_box(0),
        );
        return v___x_2186_;
    }
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed(
    mut v_toPure_2187_: *mut LeanObject,
    mut v_inst_2188_: *mut LeanObject,
    mut v_inst_2189_: *mut LeanObject,
    mut v_toBind_2190_: *mut LeanObject,
    mut v_x_2191_: *mut LeanObject,
    mut v_00_u03b3_2192_: *mut LeanObject,
    mut v_Pl_2193_: *mut LeanObject,
    mut v_it_2194_: *mut LeanObject,
    mut v_init_2195_: *mut LeanObject,
    mut v_f_2196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2197_: *mut LeanObject = core::ptr::null_mut();
    v_res_2197_ = l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2(
        v_toPure_2187_,
        v_inst_2188_,
        v_inst_2189_,
        v_toBind_2190_,
        v_x_2191_,
        v_00_u03b3_2192_,
        v_Pl_2193_,
        v_it_2194_,
        v_init_2195_,
        v_f_2196_,
    );
    lean_dec(v_x_2191_);
    return v_res_2197_;
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorLoop___redArg(
    mut v_inst_2198_: *mut LeanObject,
    mut v_inst_2199_: *mut LeanObject,
    mut v_inst_2200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2204_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2201_ = lean_ctor_get(v_inst_2200_, 0);
    lean_inc_ref(v_toApplicative_2201_);
    v_toBind_2202_ = lean_ctor_get(v_inst_2200_, 1);
    lean_inc(v_toBind_2202_);
    lean_dec_ref(v_inst_2200_);
    v_toPure_2203_ = lean_ctor_get(v_toApplicative_2201_, 1);
    lean_inc(v_toPure_2203_);
    lean_dec_ref(v_toApplicative_2201_);
    v___f_2204_ = lean_alloc_closure(
        l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed as *mut core::ffi::c_void,
        10,
        4,
    );
    lean_closure_set(v___f_2204_, 0, v_toPure_2203_);
    lean_closure_set(v___f_2204_, 1, v_inst_2199_);
    lean_closure_set(v___f_2204_, 2, v_inst_2198_);
    lean_closure_set(v___f_2204_, 3, v_toBind_2202_);
    return v___f_2204_;
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorLoop(
    mut v_00_u03b1_2205_: *mut LeanObject,
    mut v_inst_2206_: *mut LeanObject,
    mut v_inst_2207_: *mut LeanObject,
    mut v_inst_2208_: *mut LeanObject,
    mut v_inst_2209_: *mut LeanObject,
    mut v_inst_2210_: *mut LeanObject,
    mut v_n_2211_: *mut LeanObject,
    mut v_inst_2212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2216_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2213_ = lean_ctor_get(v_inst_2212_, 0);
    lean_inc_ref(v_toApplicative_2213_);
    v_toBind_2214_ = lean_ctor_get(v_inst_2212_, 1);
    lean_inc(v_toBind_2214_);
    lean_dec_ref(v_inst_2212_);
    v_toPure_2215_ = lean_ctor_get(v_toApplicative_2213_, 1);
    lean_inc(v_toPure_2215_);
    lean_dec_ref(v_toApplicative_2213_);
    v___f_2216_ = lean_alloc_closure(
        l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed as *mut core::ffi::c_void,
        10,
        4,
    );
    lean_closure_set(v___f_2216_, 0, v_toPure_2215_);
    lean_closure_set(v___f_2216_, 1, v_inst_2208_);
    lean_closure_set(v___f_2216_, 2, v_inst_2206_);
    lean_closure_set(v___f_2216_, 3, v_toBind_2214_);
    return v___f_2216_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___redArg(
    mut v_it_2217_: *mut LeanObject,
    mut v_f_2218_: *mut LeanObject,
    mut v_h__1_2219_: *mut LeanObject,
    mut v_h__2_2220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_2221_: *mut LeanObject = core::ptr::null_mut();
    v_next_2221_ = lean_ctor_get(v_it_2217_, 0);
    if lean_obj_tag(v_next_2221_) == 0 {
        let mut v_upperBound_2222_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_2219_);
        v_upperBound_2222_ = lean_ctor_get(v_it_2217_, 1);
        lean_inc(v_upperBound_2222_);
        lean_dec_ref(v_it_2217_);
        v___x_2223_ = lean_apply_2(v_h__2_2220_, v_upperBound_2222_, v_f_2218_);
        return v___x_2223_;
    } else {
        let mut v_upperBound_2224_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_2225_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_next_2221_);
        lean_dec(v_h__2_2220_);
        v_upperBound_2224_ = lean_ctor_get(v_it_2217_, 1);
        lean_inc(v_upperBound_2224_);
        lean_dec_ref(v_it_2217_);
        v_val_2225_ = lean_ctor_get(v_next_2221_, 0);
        lean_inc(v_val_2225_);
        lean_dec_ref_known(v_next_2221_, 1);
        v___x_2226_ = lean_apply_3(v_h__1_2219_, v_val_2225_, v_upperBound_2224_, v_f_2218_);
        return v___x_2226_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter(
    mut v_00_u03b1_2227_: *mut LeanObject,
    mut v_inst_2228_: *mut LeanObject,
    mut v_inst_2229_: *mut LeanObject,
    mut v_inst_2230_: *mut LeanObject,
    mut v_n_2231_: *mut LeanObject,
    mut v_00_u03b3_2232_: *mut LeanObject,
    mut v_Pl_2233_: *mut LeanObject,
    mut v_motive_2234_: *mut LeanObject,
    mut v_it_2235_: *mut LeanObject,
    mut v_f_2236_: *mut LeanObject,
    mut v_h__1_2237_: *mut LeanObject,
    mut v_h__2_2238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_2239_: *mut LeanObject = core::ptr::null_mut();
    v_next_2239_ = lean_ctor_get(v_it_2235_, 0);
    if lean_obj_tag(v_next_2239_) == 0 {
        let mut v_upperBound_2240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_2237_);
        v_upperBound_2240_ = lean_ctor_get(v_it_2235_, 1);
        lean_inc(v_upperBound_2240_);
        lean_dec_ref(v_it_2235_);
        v___x_2241_ = lean_apply_2(v_h__2_2238_, v_upperBound_2240_, v_f_2236_);
        return v___x_2241_;
    } else {
        let mut v_upperBound_2242_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_2243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_next_2239_);
        lean_dec(v_h__2_2238_);
        v_upperBound_2242_ = lean_ctor_get(v_it_2235_, 1);
        lean_inc(v_upperBound_2242_);
        lean_dec_ref(v_it_2235_);
        v_val_2243_ = lean_ctor_get(v_next_2239_, 0);
        lean_inc(v_val_2243_);
        lean_dec_ref_known(v_next_2239_, 1);
        v___x_2244_ = lean_apply_3(v_h__1_2237_, v_val_2243_, v_upperBound_2242_, v_f_2236_);
        return v___x_2244_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___boxed(
    mut v_00_u03b1_2245_: *mut LeanObject,
    mut v_inst_2246_: *mut LeanObject,
    mut v_inst_2247_: *mut LeanObject,
    mut v_inst_2248_: *mut LeanObject,
    mut v_n_2249_: *mut LeanObject,
    mut v_00_u03b3_2250_: *mut LeanObject,
    mut v_Pl_2251_: *mut LeanObject,
    mut v_motive_2252_: *mut LeanObject,
    mut v_it_2253_: *mut LeanObject,
    mut v_f_2254_: *mut LeanObject,
    mut v_h__1_2255_: *mut LeanObject,
    mut v_h__2_2256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2257_: *mut LeanObject = core::ptr::null_mut();
    v_res_2257_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_2245_, v_inst_2246_, v_inst_2247_, v_inst_2248_, v_n_2249_, v_00_u03b3_2250_, v_Pl_2251_, v_motive_2252_, v_it_2253_, v_f_2254_, v_h__1_2255_, v_h__2_2256_);
    lean_dec_ref(v_inst_2248_);
    lean_dec_ref(v_inst_2246_);
    return v_res_2257_;
}
pub unsafe fn l_Std_Rxi_Iterator_Monadic_step___redArg(
    mut v_inst_2258_: *mut LeanObject,
    mut v_it_2259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut v_unused_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_it_2259_) == 0 {
                    lean_dec_ref(v_inst_2258_);
                    v___x_2260_ = lean_box(2);
                    return v___x_2260_;
                } else {
                    v_val_2261_ = lean_ctor_get(v_it_2259_, 0);
                    lean_inc(v_val_2261_);
                    lean_dec_ref_known(v_it_2259_, 1);
                    v_succ_x3f_2262_ = lean_ctor_get(v_inst_2258_, 0);
                    v_isSharedCheck_2270_ = (!lean_is_exclusive(v_inst_2258_)) as u8;
                    if v_isSharedCheck_2270_ == 0 {
                        v_unused_2271_ = lean_ctor_get(v_inst_2258_, 1);
                        lean_dec(v_unused_2271_);
                        v___x_2264_ = v_inst_2258_;
                        v_isShared_2265_ = v_isSharedCheck_2270_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_succ_x3f_2262_);
                        lean_dec(v_inst_2258_);
                        v___x_2264_ = lean_box(0);
                        v_isShared_2265_ = v_isSharedCheck_2270_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_val_2261_);
                v___x_2266_ = lean_apply_1(v_succ_x3f_2262_, v_val_2261_);
                if v_isShared_2265_ == 0 {
                    lean_ctor_set(v___x_2264_, 1, v_val_2261_);
                    lean_ctor_set(v___x_2264_, 0, v___x_2266_);
                    v___x_2268_ = v___x_2264_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
                    lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_val_2261_);
                    v___x_2268_ = v_reuseFailAlloc_2269_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxi_Iterator_Monadic_step(
    mut v_00_u03b1_2272_: *mut LeanObject,
    mut v_inst_2273_: *mut LeanObject,
    mut v_it_2274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2280_: u8 = 0;
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2285_: u8 = 0;
    let mut v_unused_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_it_2274_) == 0 {
                    lean_dec_ref(v_inst_2273_);
                    v___x_2275_ = lean_box(2);
                    return v___x_2275_;
                } else {
                    v_val_2276_ = lean_ctor_get(v_it_2274_, 0);
                    lean_inc(v_val_2276_);
                    lean_dec_ref_known(v_it_2274_, 1);
                    v_succ_x3f_2277_ = lean_ctor_get(v_inst_2273_, 0);
                    v_isSharedCheck_2285_ = (!lean_is_exclusive(v_inst_2273_)) as u8;
                    if v_isSharedCheck_2285_ == 0 {
                        v_unused_2286_ = lean_ctor_get(v_inst_2273_, 1);
                        lean_dec(v_unused_2286_);
                        v___x_2279_ = v_inst_2273_;
                        v_isShared_2280_ = v_isSharedCheck_2285_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_succ_x3f_2277_);
                        lean_dec(v_inst_2273_);
                        v___x_2279_ = lean_box(0);
                        v_isShared_2280_ = v_isSharedCheck_2285_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_val_2276_);
                v___x_2281_ = lean_apply_1(v_succ_x3f_2277_, v_val_2276_);
                if v_isShared_2280_ == 0 {
                    lean_ctor_set(v___x_2279_, 1, v_val_2276_);
                    lean_ctor_set(v___x_2279_, 0, v___x_2281_);
                    v___x_2283_ = v___x_2279_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
                    lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_val_2276_);
                    v___x_2283_ = v_reuseFailAlloc_2284_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2283_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxi_Iterator_step___redArg(
    mut v_inst_2287_: *mut LeanObject,
    mut v_it_2288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2294_: u8 = 0;
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut v_unused_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_it_2288_) == 0 {
                    lean_dec_ref(v_inst_2287_);
                    v___x_2289_ = lean_box(2);
                    return v___x_2289_;
                } else {
                    v_val_2290_ = lean_ctor_get(v_it_2288_, 0);
                    lean_inc(v_val_2290_);
                    lean_dec_ref_known(v_it_2288_, 1);
                    v_succ_x3f_2291_ = lean_ctor_get(v_inst_2287_, 0);
                    v_isSharedCheck_2299_ = (!lean_is_exclusive(v_inst_2287_)) as u8;
                    if v_isSharedCheck_2299_ == 0 {
                        v_unused_2300_ = lean_ctor_get(v_inst_2287_, 1);
                        lean_dec(v_unused_2300_);
                        v___x_2293_ = v_inst_2287_;
                        v_isShared_2294_ = v_isSharedCheck_2299_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_succ_x3f_2291_);
                        lean_dec(v_inst_2287_);
                        v___x_2293_ = lean_box(0);
                        v_isShared_2294_ = v_isSharedCheck_2299_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_val_2290_);
                v___x_2295_ = lean_apply_1(v_succ_x3f_2291_, v_val_2290_);
                if v_isShared_2294_ == 0 {
                    lean_ctor_set(v___x_2293_, 1, v_val_2290_);
                    lean_ctor_set(v___x_2293_, 0, v___x_2295_);
                    v___x_2297_ = v___x_2293_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_val_2290_);
                    v___x_2297_ = v_reuseFailAlloc_2298_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2297_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxi_Iterator_step(
    mut v_00_u03b1_2301_: *mut LeanObject,
    mut v_inst_2302_: *mut LeanObject,
    mut v_it_2303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2309_: u8 = 0;
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2314_: u8 = 0;
    let mut v_unused_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_it_2303_) == 0 {
                    lean_dec_ref(v_inst_2302_);
                    v___x_2304_ = lean_box(2);
                    return v___x_2304_;
                } else {
                    v_val_2305_ = lean_ctor_get(v_it_2303_, 0);
                    lean_inc(v_val_2305_);
                    lean_dec_ref_known(v_it_2303_, 1);
                    v_succ_x3f_2306_ = lean_ctor_get(v_inst_2302_, 0);
                    v_isSharedCheck_2314_ = (!lean_is_exclusive(v_inst_2302_)) as u8;
                    if v_isSharedCheck_2314_ == 0 {
                        v_unused_2315_ = lean_ctor_get(v_inst_2302_, 1);
                        lean_dec(v_unused_2315_);
                        v___x_2308_ = v_inst_2302_;
                        v_isShared_2309_ = v_isSharedCheck_2314_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_succ_x3f_2306_);
                        lean_dec(v_inst_2302_);
                        v___x_2308_ = lean_box(0);
                        v_isShared_2309_ = v_isSharedCheck_2314_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_val_2305_);
                v___x_2310_ = lean_apply_1(v_succ_x3f_2306_, v_val_2305_);
                if v_isShared_2309_ == 0 {
                    lean_ctor_set(v___x_2308_, 1, v_val_2305_);
                    lean_ctor_set(v___x_2308_, 0, v___x_2310_);
                    v___x_2312_ = v___x_2308_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
                    lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_val_2305_);
                    v___x_2312_ = v_reuseFailAlloc_2313_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2312_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0(
    mut v_inst_2316_: *mut LeanObject,
    mut v_it_2317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2323_: u8 = 0;
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2328_: u8 = 0;
    let mut v_unused_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_it_2317_) == 0 {
                    lean_dec_ref(v_inst_2316_);
                    v___x_2318_ = lean_box(2);
                    return v___x_2318_;
                } else {
                    v_val_2319_ = lean_ctor_get(v_it_2317_, 0);
                    lean_inc(v_val_2319_);
                    lean_dec_ref_known(v_it_2317_, 1);
                    v_succ_x3f_2320_ = lean_ctor_get(v_inst_2316_, 0);
                    v_isSharedCheck_2328_ = (!lean_is_exclusive(v_inst_2316_)) as u8;
                    if v_isSharedCheck_2328_ == 0 {
                        v_unused_2329_ = lean_ctor_get(v_inst_2316_, 1);
                        lean_dec(v_unused_2329_);
                        v___x_2322_ = v_inst_2316_;
                        v_isShared_2323_ = v_isSharedCheck_2328_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_succ_x3f_2320_);
                        lean_dec(v_inst_2316_);
                        v___x_2322_ = lean_box(0);
                        v_isShared_2323_ = v_isSharedCheck_2328_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_val_2319_);
                v___x_2324_ = lean_apply_1(v_succ_x3f_2320_, v_val_2319_);
                if v_isShared_2323_ == 0 {
                    lean_ctor_set(v___x_2322_, 1, v_val_2319_);
                    lean_ctor_set(v___x_2322_, 0, v___x_2324_);
                    v___x_2326_ = v___x_2322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
                    lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_val_2319_);
                    v___x_2326_ = v_reuseFailAlloc_2327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg(
    mut v_inst_2330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2331_: *mut LeanObject = core::ptr::null_mut();
    v___f_2331_ = lean_alloc_closure(
        l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2331_, 0, v_inst_2330_);
    return v___f_2331_;
}
pub unsafe fn l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable(
    mut v_00_u03b1_2332_: *mut LeanObject,
    mut v_inst_2333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2334_: *mut LeanObject = core::ptr::null_mut();
    v___f_2334_ = lean_alloc_closure(
        l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2334_, 0, v_inst_2333_);
    return v___f_2334_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation(
    mut v_00_u03b1_2335_: *mut LeanObject,
    mut v_inst_2336_: *mut LeanObject,
    mut v_inst_2337_: *mut LeanObject,
    mut v_inst_2338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    v___x_2339_ = lean_box(0);
    return v___x_2339_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___boxed(
    mut v_00_u03b1_2340_: *mut LeanObject,
    mut v_inst_2341_: *mut LeanObject,
    mut v_inst_2342_: *mut LeanObject,
    mut v_inst_2343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2344_: *mut LeanObject = core::ptr::null_mut();
    v_res_2344_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation(v_00_u03b1_2340_, v_inst_2341_, v_inst_2342_, v_inst_2343_);
    lean_dec_ref(v_inst_2341_);
    return v_res_2344_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation(
    mut v_00_u03b1_2345_: *mut LeanObject,
    mut v_inst_2346_: *mut LeanObject,
    mut v_inst_2347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    v___x_2348_ = lean_box(0);
    return v___x_2348_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___boxed(
    mut v_00_u03b1_2349_: *mut LeanObject,
    mut v_inst_2350_: *mut LeanObject,
    mut v_inst_2351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2352_: *mut LeanObject = core::ptr::null_mut();
    v_res_2352_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation(v_00_u03b1_2349_, v_inst_2350_, v_inst_2351_);
    lean_dec_ref(v_inst_2350_);
    return v_res_2352_;
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0(
    mut v_inst_2353_: *mut LeanObject,
    mut v_it_2354_: *mut LeanObject,
    mut v_n_2355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_succMany_x3f_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2361_: u8 = 0;
    let mut v_val_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_it_2354_) == 0 {
                    lean_dec(v_n_2355_);
                    lean_dec_ref(v_inst_2353_);
                    v___x_2356_ = lean_box(2);
                    return v___x_2356_;
                } else {
                    v_succ_x3f_2357_ = lean_ctor_get(v_inst_2353_, 0);
                    v_succMany_x3f_2358_ = lean_ctor_get(v_inst_2353_, 1);
                    v_isSharedCheck_2370_ = (!lean_is_exclusive(v_inst_2353_)) as u8;
                    if v_isSharedCheck_2370_ == 0 {
                        v___x_2360_ = v_inst_2353_;
                        v_isShared_2361_ = v_isSharedCheck_2370_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_succMany_x3f_2358_);
                        lean_inc(v_succ_x3f_2357_);
                        lean_dec(v_inst_2353_);
                        v___x_2360_ = lean_box(0);
                        v_isShared_2361_ = v_isSharedCheck_2370_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_2362_ = lean_ctor_get(v_it_2354_, 0);
                lean_inc(v_val_2362_);
                lean_dec_ref_known(v_it_2354_, 1);
                v___x_2363_ = lean_apply_2(v_succMany_x3f_2358_, v_n_2355_, v_val_2362_);
                if lean_obj_tag(v___x_2363_) == 0 {
                    lean_del_object(v___x_2360_);
                    lean_dec_ref(v_succ_x3f_2357_);
                    v___x_2364_ = lean_box(2);
                    return v___x_2364_;
                } else {
                    v_val_2365_ = lean_ctor_get(v___x_2363_, 0);
                    lean_inc_n(v_val_2365_, 2);
                    lean_dec_ref_known(v___x_2363_, 1);
                    v___x_2366_ = lean_apply_1(v_succ_x3f_2357_, v_val_2365_);
                    if v_isShared_2361_ == 0 {
                        lean_ctor_set(v___x_2360_, 1, v_val_2365_);
                        lean_ctor_set(v___x_2360_, 0, v___x_2366_);
                        v___x_2368_ = v___x_2360_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
                        lean_ctor_set(v_reuseFailAlloc_2369_, 1, v_val_2365_);
                        v___x_2368_ = v_reuseFailAlloc_2369_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorAccess___redArg(
    mut v_inst_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2372_: *mut LeanObject = core::ptr::null_mut();
    v___f_2372_ = lean_alloc_closure(
        l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2372_, 0, v_inst_2371_);
    return v___f_2372_;
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorAccess(
    mut v_00_u03b1_2373_: *mut LeanObject,
    mut v_inst_2374_: *mut LeanObject,
    mut v_inst_2375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2376_: *mut LeanObject = core::ptr::null_mut();
    v___f_2376_ = lean_alloc_closure(
        l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2376_, 0, v_inst_2374_);
    return v___f_2376_;
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1(
    mut v_toPure_2377_: *mut LeanObject,
    mut v_inst_2378_: *mut LeanObject,
    mut v_f_2379_: *mut LeanObject,
    mut v_toBind_2380_: *mut LeanObject,
    mut v_next_2381_: *mut LeanObject,
    mut v_acc_2382_: *mut LeanObject,
    mut v_h_2383_: *mut LeanObject,
    mut v_G_2384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_next_2381_);
    v___f_2385_ = lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2385_, 0, v_toPure_2377_);
    lean_closure_set(v___f_2385_, 1, v_inst_2378_);
    lean_closure_set(v___f_2385_, 2, v_next_2381_);
    lean_closure_set(v___f_2385_, 3, v_G_2384_);
    v___x_2386_ = lean_apply_3(v_f_2379_, v_next_2381_, lean_box(0), v_acc_2382_);
    v___x_2387_ = lean_apply_4(
        v_toBind_2380_,
        lean_box(0),
        lean_box(0),
        v___x_2386_,
        v___f_2385_,
    );
    return v___x_2387_;
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg(
    mut v_inst_2388_: *mut LeanObject,
    mut v_inst_2389_: *mut LeanObject,
    mut v_acc_2390_: *mut LeanObject,
    mut v_next_2391_: *mut LeanObject,
    mut v_f_2392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2393_ = lean_ctor_get(v_inst_2389_, 0);
    lean_inc_ref(v_toApplicative_2393_);
    v_toBind_2394_ = lean_ctor_get(v_inst_2389_, 1);
    lean_inc(v_toBind_2394_);
    lean_dec_ref(v_inst_2389_);
    v_toPure_2395_ = lean_ctor_get(v_toApplicative_2393_, 1);
    lean_inc(v_toPure_2395_);
    lean_dec_ref(v_toApplicative_2393_);
    v___f_2396_ = lean_alloc_closure(
        l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_2396_, 0, v_toPure_2395_);
    lean_closure_set(v___f_2396_, 1, v_inst_2388_);
    lean_closure_set(v___f_2396_, 2, v_f_2392_);
    lean_closure_set(v___f_2396_, 3, v_toBind_2394_);
    v___x_2397_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_2396_, v_next_2391_, v_acc_2390_, lean_box(0));
    return v___x_2397_;
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorLoop_loop(
    mut v_00_u03b1_2398_: *mut LeanObject,
    mut v_inst_2399_: *mut LeanObject,
    mut v_inst_2400_: *mut LeanObject,
    mut v_n_2401_: *mut LeanObject,
    mut v_inst_2402_: *mut LeanObject,
    mut v_00_u03b3_2403_: *mut LeanObject,
    mut v_Pl_2404_: *mut LeanObject,
    mut v_LargeEnough_2405_: *mut LeanObject,
    mut v_hl_2406_: *mut LeanObject,
    mut v_acc_2407_: *mut LeanObject,
    mut v_next_2408_: *mut LeanObject,
    mut v_h_2409_: *mut LeanObject,
    mut v_f_2410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2411_ = lean_ctor_get(v_inst_2402_, 0);
    lean_inc_ref(v_toApplicative_2411_);
    v_toBind_2412_ = lean_ctor_get(v_inst_2402_, 1);
    lean_inc(v_toBind_2412_);
    lean_dec_ref(v_inst_2402_);
    v_toPure_2413_ = lean_ctor_get(v_toApplicative_2411_, 1);
    lean_inc(v_toPure_2413_);
    lean_dec_ref(v_toApplicative_2411_);
    v___f_2414_ = lean_alloc_closure(
        l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_2414_, 0, v_toPure_2413_);
    lean_closure_set(v___f_2414_, 1, v_inst_2399_);
    lean_closure_set(v___f_2414_, 2, v_f_2410_);
    lean_closure_set(v___f_2414_, 3, v_toBind_2412_);
    v___x_2415_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_2414_, v_next_2408_, v_acc_2407_, lean_box(0));
    return v___x_2415_;
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2(
    mut v_toPure_2416_: *mut LeanObject,
    mut v_inst_2417_: *mut LeanObject,
    mut v_toBind_2418_: *mut LeanObject,
    mut v_x_2419_: *mut LeanObject,
    mut v_00_u03b3_2420_: *mut LeanObject,
    mut v_Pl_2421_: *mut LeanObject,
    mut v_it_2422_: *mut LeanObject,
    mut v_init_2423_: *mut LeanObject,
    mut v_f_2424_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_2422_) == 0 {
        let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_2424_);
        lean_dec(v_toBind_2418_);
        lean_dec_ref(v_inst_2417_);
        v___x_2425_ = lean_apply_2(v_toPure_2416_, lean_box(0), v_init_2423_);
        return v___x_2425_;
    } else {
        let mut v_val_2426_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
        v_val_2426_ = lean_ctor_get(v_it_2422_, 0);
        lean_inc(v_val_2426_);
        lean_dec_ref_known(v_it_2422_, 1);
        v___f_2427_ = lean_alloc_closure(
            l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1 as *mut core::ffi::c_void,
            8,
            4,
        );
        lean_closure_set(v___f_2427_, 0, v_toPure_2416_);
        lean_closure_set(v___f_2427_, 1, v_inst_2417_);
        lean_closure_set(v___f_2427_, 2, v_f_2424_);
        lean_closure_set(v___f_2427_, 3, v_toBind_2418_);
        v___x_2428_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_2427_,
            v_val_2426_,
            v_init_2423_,
            lean_box(0),
        );
        return v___x_2428_;
    }
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed(
    mut v_toPure_2429_: *mut LeanObject,
    mut v_inst_2430_: *mut LeanObject,
    mut v_toBind_2431_: *mut LeanObject,
    mut v_x_2432_: *mut LeanObject,
    mut v_00_u03b3_2433_: *mut LeanObject,
    mut v_Pl_2434_: *mut LeanObject,
    mut v_it_2435_: *mut LeanObject,
    mut v_init_2436_: *mut LeanObject,
    mut v_f_2437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2438_: *mut LeanObject = core::ptr::null_mut();
    v_res_2438_ = l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2(
        v_toPure_2429_,
        v_inst_2430_,
        v_toBind_2431_,
        v_x_2432_,
        v_00_u03b3_2433_,
        v_Pl_2434_,
        v_it_2435_,
        v_init_2436_,
        v_f_2437_,
    );
    lean_dec(v_x_2432_);
    return v_res_2438_;
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorLoop___redArg(
    mut v_inst_2439_: *mut LeanObject,
    mut v_inst_2440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2444_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2441_ = lean_ctor_get(v_inst_2440_, 0);
    lean_inc_ref(v_toApplicative_2441_);
    v_toBind_2442_ = lean_ctor_get(v_inst_2440_, 1);
    lean_inc(v_toBind_2442_);
    lean_dec_ref(v_inst_2440_);
    v_toPure_2443_ = lean_ctor_get(v_toApplicative_2441_, 1);
    lean_inc(v_toPure_2443_);
    lean_dec_ref(v_toApplicative_2441_);
    v___f_2444_ = lean_alloc_closure(
        l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed as *mut core::ffi::c_void,
        9,
        3,
    );
    lean_closure_set(v___f_2444_, 0, v_toPure_2443_);
    lean_closure_set(v___f_2444_, 1, v_inst_2439_);
    lean_closure_set(v___f_2444_, 2, v_toBind_2442_);
    return v___f_2444_;
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorLoop(
    mut v_00_u03b1_2445_: *mut LeanObject,
    mut v_inst_2446_: *mut LeanObject,
    mut v_inst_2447_: *mut LeanObject,
    mut v_n_2448_: *mut LeanObject,
    mut v_inst_2449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2453_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2450_ = lean_ctor_get(v_inst_2449_, 0);
    lean_inc_ref(v_toApplicative_2450_);
    v_toBind_2451_ = lean_ctor_get(v_inst_2449_, 1);
    lean_inc(v_toBind_2451_);
    lean_dec_ref(v_inst_2449_);
    v_toPure_2452_ = lean_ctor_get(v_toApplicative_2450_, 1);
    lean_inc(v_toPure_2452_);
    lean_dec_ref(v_toApplicative_2450_);
    v___f_2453_ = lean_alloc_closure(
        l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed as *mut core::ffi::c_void,
        9,
        3,
    );
    lean_closure_set(v___f_2453_, 0, v_toPure_2452_);
    lean_closure_set(v___f_2453_, 1, v_inst_2446_);
    lean_closure_set(v___f_2453_, 2, v_toBind_2451_);
    return v___f_2453_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___redArg(
    mut v_it_2454_: *mut LeanObject,
    mut v_f_2455_: *mut LeanObject,
    mut v_h__1_2456_: *mut LeanObject,
    mut v_h__2_2457_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_2454_) == 0 {
        let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_2456_);
        v___x_2458_ = lean_apply_1(v_h__2_2457_, v_f_2455_);
        return v___x_2458_;
    } else {
        let mut v_val_2459_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_2457_);
        v_val_2459_ = lean_ctor_get(v_it_2454_, 0);
        lean_inc(v_val_2459_);
        lean_dec_ref_known(v_it_2454_, 1);
        v___x_2460_ = lean_apply_2(v_h__1_2456_, v_val_2459_, v_f_2455_);
        return v___x_2460_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter(
    mut v_00_u03b1_2461_: *mut LeanObject,
    mut v_inst_2462_: *mut LeanObject,
    mut v_n_2463_: *mut LeanObject,
    mut v_00_u03b3_2464_: *mut LeanObject,
    mut v_Pl_2465_: *mut LeanObject,
    mut v_motive_2466_: *mut LeanObject,
    mut v_it_2467_: *mut LeanObject,
    mut v_f_2468_: *mut LeanObject,
    mut v_h__1_2469_: *mut LeanObject,
    mut v_h__2_2470_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_2467_) == 0 {
        let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_2469_);
        v___x_2471_ = lean_apply_1(v_h__2_2470_, v_f_2468_);
        return v___x_2471_;
    } else {
        let mut v_val_2472_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_2470_);
        v_val_2472_ = lean_ctor_get(v_it_2467_, 0);
        lean_inc(v_val_2472_);
        lean_dec_ref_known(v_it_2467_, 1);
        v___x_2473_ = lean_apply_2(v_h__1_2469_, v_val_2472_, v_f_2468_);
        return v___x_2473_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___boxed(
    mut v_00_u03b1_2474_: *mut LeanObject,
    mut v_inst_2475_: *mut LeanObject,
    mut v_n_2476_: *mut LeanObject,
    mut v_00_u03b3_2477_: *mut LeanObject,
    mut v_Pl_2478_: *mut LeanObject,
    mut v_motive_2479_: *mut LeanObject,
    mut v_it_2480_: *mut LeanObject,
    mut v_f_2481_: *mut LeanObject,
    mut v_h__1_2482_: *mut LeanObject,
    mut v_h__2_2483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2484_: *mut LeanObject = core::ptr::null_mut();
    v_res_2484_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_2474_, v_inst_2475_, v_n_2476_, v_00_u03b3_2477_, v_Pl_2478_, v_motive_2479_, v_it_2480_, v_f_2481_, v_h__1_2482_, v_h__2_2483_);
    lean_dec_ref(v_inst_2475_);
    return v_res_2484_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_PRange(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_RangeIterator(
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
pub unsafe fn initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_PRange(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
}
