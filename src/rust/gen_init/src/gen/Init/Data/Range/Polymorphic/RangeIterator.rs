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
pub unsafe fn l_Std_Rxc_Iterator_Monadic_step___redArg(
    mut v_inst_1243_: *mut leanh::LeanObject,
    mut v_inst_1244_: *mut leanh::LeanObject,
    mut v_it_1245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1251_: u8 = 0;
    let mut v_val_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: u8 = 0;
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1259_: u8 = 0;
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1267_: u8 = 0;
    let mut v_unused_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1269_: u8 = 0;
    let mut v_unused_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1246_ = leanh::lean_ctor_get(v_it_1245_, 0);
                leanh::lean_inc(v_next_1246_);
                if leanh::lean_obj_tag(v_next_1246_) == 0 {
                    leanh::lean_dec_ref(v_it_1245_);
                    leanh::lean_dec_ref(v_inst_1244_);
                    leanh::lean_dec_ref(v_inst_1243_);
                    v___x_1247_ = leanh::lean_box(2);
                    return v___x_1247_;
                } else {
                    v_upperBound_1248_ = leanh::lean_ctor_get(v_it_1245_, 1);
                    v_isSharedCheck_1269_ = (!leanh::lean_is_exclusive(v_it_1245_)) as u8;
                    if v_isSharedCheck_1269_ == 0 {
                        v_unused_1270_ = leanh::lean_ctor_get(v_it_1245_, 0);
                        leanh::lean_dec(v_unused_1270_);
                        v___x_1250_ = v_it_1245_;
                        v_isShared_1251_ = v_isSharedCheck_1269_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_upperBound_1248_);
                        leanh::lean_dec(v_it_1245_);
                        v___x_1250_ = leanh::lean_box(0);
                        v_isShared_1251_ = v_isSharedCheck_1269_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1252_ = leanh::lean_ctor_get(v_next_1246_, 0);
                leanh::lean_inc_n(v_val_1252_, 2);
                leanh::lean_dec_ref_known(v_next_1246_, 1);
                leanh::lean_inc(v_upperBound_1248_);
                v___x_1253_ =
                    leanh::lean_apply_2(v_inst_1244_, v_val_1252_, v_upperBound_1248_);
                v___x_1254_ = (leanh::lean_unbox(v___x_1253_) as u8);
                if v___x_1254_ == 0 {
                    leanh::lean_dec(v_val_1252_);
                    leanh::lean_del_object(v___x_1250_);
                    leanh::lean_dec(v_upperBound_1248_);
                    leanh::lean_dec_ref(v_inst_1243_);
                    v___x_1255_ = leanh::lean_box(2);
                    return v___x_1255_;
                } else {
                    v_succ_x3f_1256_ = leanh::lean_ctor_get(v_inst_1243_, 0);
                    v_isSharedCheck_1267_ = (!leanh::lean_is_exclusive(v_inst_1243_)) as u8;
                    if v_isSharedCheck_1267_ == 0 {
                        v_unused_1268_ = leanh::lean_ctor_get(v_inst_1243_, 1);
                        leanh::lean_dec(v_unused_1268_);
                        v___x_1258_ = v_inst_1243_;
                        v_isShared_1259_ = v_isSharedCheck_1267_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_succ_x3f_1256_);
                        leanh::lean_dec(v_inst_1243_);
                        v___x_1258_ = leanh::lean_box(0);
                        v_isShared_1259_ = v_isSharedCheck_1267_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_val_1252_);
                v___x_1260_ = leanh::lean_apply_1(v_succ_x3f_1256_, v_val_1252_);
                if v_isShared_1251_ == 0 {
                    leanh::lean_ctor_set(v___x_1250_, 0, v___x_1260_);
                    v___x_1262_ = v___x_1250_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1266_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1260_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_upperBound_1248_);
                    v___x_1262_ = v_reuseFailAlloc_1266_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1259_ == 0 {
                    leanh::lean_ctor_set(v___x_1258_, 1, v_val_1252_);
                    leanh::lean_ctor_set(v___x_1258_, 0, v___x_1262_);
                    v___x_1264_ = v___x_1258_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1265_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_val_1252_);
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
    mut v_00_u03b1_1271_: *mut leanh::LeanObject,
    mut v_inst_1272_: *mut leanh::LeanObject,
    mut v_inst_1273_: *mut leanh::LeanObject,
    mut v_inst_1274_: *mut leanh::LeanObject,
    mut v_it_1275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1281_: u8 = 0;
    let mut v_val_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: u8 = 0;
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1289_: u8 = 0;
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1297_: u8 = 0;
    let mut v_unused_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1299_: u8 = 0;
    let mut v_unused_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1276_ = leanh::lean_ctor_get(v_it_1275_, 0);
                leanh::lean_inc(v_next_1276_);
                if leanh::lean_obj_tag(v_next_1276_) == 0 {
                    leanh::lean_dec_ref(v_it_1275_);
                    leanh::lean_dec_ref(v_inst_1274_);
                    leanh::lean_dec_ref(v_inst_1272_);
                    v___x_1277_ = leanh::lean_box(2);
                    return v___x_1277_;
                } else {
                    v_upperBound_1278_ = leanh::lean_ctor_get(v_it_1275_, 1);
                    v_isSharedCheck_1299_ = (!leanh::lean_is_exclusive(v_it_1275_)) as u8;
                    if v_isSharedCheck_1299_ == 0 {
                        v_unused_1300_ = leanh::lean_ctor_get(v_it_1275_, 0);
                        leanh::lean_dec(v_unused_1300_);
                        v___x_1280_ = v_it_1275_;
                        v_isShared_1281_ = v_isSharedCheck_1299_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_upperBound_1278_);
                        leanh::lean_dec(v_it_1275_);
                        v___x_1280_ = leanh::lean_box(0);
                        v_isShared_1281_ = v_isSharedCheck_1299_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1282_ = leanh::lean_ctor_get(v_next_1276_, 0);
                leanh::lean_inc_n(v_val_1282_, 2);
                leanh::lean_dec_ref_known(v_next_1276_, 1);
                leanh::lean_inc(v_upperBound_1278_);
                v___x_1283_ =
                    leanh::lean_apply_2(v_inst_1274_, v_val_1282_, v_upperBound_1278_);
                v___x_1284_ = (leanh::lean_unbox(v___x_1283_) as u8);
                if v___x_1284_ == 0 {
                    leanh::lean_dec(v_val_1282_);
                    leanh::lean_del_object(v___x_1280_);
                    leanh::lean_dec(v_upperBound_1278_);
                    leanh::lean_dec_ref(v_inst_1272_);
                    v___x_1285_ = leanh::lean_box(2);
                    return v___x_1285_;
                } else {
                    v_succ_x3f_1286_ = leanh::lean_ctor_get(v_inst_1272_, 0);
                    v_isSharedCheck_1297_ = (!leanh::lean_is_exclusive(v_inst_1272_)) as u8;
                    if v_isSharedCheck_1297_ == 0 {
                        v_unused_1298_ = leanh::lean_ctor_get(v_inst_1272_, 1);
                        leanh::lean_dec(v_unused_1298_);
                        v___x_1288_ = v_inst_1272_;
                        v_isShared_1289_ = v_isSharedCheck_1297_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_succ_x3f_1286_);
                        leanh::lean_dec(v_inst_1272_);
                        v___x_1288_ = leanh::lean_box(0);
                        v_isShared_1289_ = v_isSharedCheck_1297_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_val_1282_);
                v___x_1290_ = leanh::lean_apply_1(v_succ_x3f_1286_, v_val_1282_);
                if v_isShared_1281_ == 0 {
                    leanh::lean_ctor_set(v___x_1280_, 0, v___x_1290_);
                    v___x_1292_ = v___x_1280_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1296_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1290_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_upperBound_1278_);
                    v___x_1292_ = v_reuseFailAlloc_1296_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1289_ == 0 {
                    leanh::lean_ctor_set(v___x_1288_, 1, v_val_1282_);
                    leanh::lean_ctor_set(v___x_1288_, 0, v___x_1292_);
                    v___x_1294_ = v___x_1288_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1295_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_val_1282_);
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
    mut v_inst_1301_: *mut leanh::LeanObject,
    mut v_inst_1302_: *mut leanh::LeanObject,
    mut v_it_1303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1309_: u8 = 0;
    let mut v_val_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: u8 = 0;
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1317_: u8 = 0;
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1325_: u8 = 0;
    let mut v_unused_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1327_: u8 = 0;
    let mut v_unused_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1304_ = leanh::lean_ctor_get(v_it_1303_, 0);
                leanh::lean_inc(v_next_1304_);
                if leanh::lean_obj_tag(v_next_1304_) == 0 {
                    leanh::lean_dec_ref(v_it_1303_);
                    leanh::lean_dec_ref(v_inst_1302_);
                    leanh::lean_dec_ref(v_inst_1301_);
                    v___x_1305_ = leanh::lean_box(2);
                    return v___x_1305_;
                } else {
                    v_upperBound_1306_ = leanh::lean_ctor_get(v_it_1303_, 1);
                    v_isSharedCheck_1327_ = (!leanh::lean_is_exclusive(v_it_1303_)) as u8;
                    if v_isSharedCheck_1327_ == 0 {
                        v_unused_1328_ = leanh::lean_ctor_get(v_it_1303_, 0);
                        leanh::lean_dec(v_unused_1328_);
                        v___x_1308_ = v_it_1303_;
                        v_isShared_1309_ = v_isSharedCheck_1327_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_upperBound_1306_);
                        leanh::lean_dec(v_it_1303_);
                        v___x_1308_ = leanh::lean_box(0);
                        v_isShared_1309_ = v_isSharedCheck_1327_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1310_ = leanh::lean_ctor_get(v_next_1304_, 0);
                leanh::lean_inc_n(v_val_1310_, 2);
                leanh::lean_dec_ref_known(v_next_1304_, 1);
                leanh::lean_inc(v_upperBound_1306_);
                v___x_1311_ =
                    leanh::lean_apply_2(v_inst_1302_, v_val_1310_, v_upperBound_1306_);
                v___x_1312_ = (leanh::lean_unbox(v___x_1311_) as u8);
                if v___x_1312_ == 0 {
                    leanh::lean_dec(v_val_1310_);
                    leanh::lean_del_object(v___x_1308_);
                    leanh::lean_dec(v_upperBound_1306_);
                    leanh::lean_dec_ref(v_inst_1301_);
                    v___x_1313_ = leanh::lean_box(2);
                    return v___x_1313_;
                } else {
                    v_succ_x3f_1314_ = leanh::lean_ctor_get(v_inst_1301_, 0);
                    v_isSharedCheck_1325_ = (!leanh::lean_is_exclusive(v_inst_1301_)) as u8;
                    if v_isSharedCheck_1325_ == 0 {
                        v_unused_1326_ = leanh::lean_ctor_get(v_inst_1301_, 1);
                        leanh::lean_dec(v_unused_1326_);
                        v___x_1316_ = v_inst_1301_;
                        v_isShared_1317_ = v_isSharedCheck_1325_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_succ_x3f_1314_);
                        leanh::lean_dec(v_inst_1301_);
                        v___x_1316_ = leanh::lean_box(0);
                        v_isShared_1317_ = v_isSharedCheck_1325_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_val_1310_);
                v___x_1318_ = leanh::lean_apply_1(v_succ_x3f_1314_, v_val_1310_);
                if v_isShared_1309_ == 0 {
                    leanh::lean_ctor_set(v___x_1308_, 0, v___x_1318_);
                    v___x_1320_ = v___x_1308_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1324_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1318_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_upperBound_1306_);
                    v___x_1320_ = v_reuseFailAlloc_1324_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1317_ == 0 {
                    leanh::lean_ctor_set(v___x_1316_, 1, v_val_1310_);
                    leanh::lean_ctor_set(v___x_1316_, 0, v___x_1320_);
                    v___x_1322_ = v___x_1316_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1323_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_val_1310_);
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
    mut v_00_u03b1_1329_: *mut leanh::LeanObject,
    mut v_inst_1330_: *mut leanh::LeanObject,
    mut v_inst_1331_: *mut leanh::LeanObject,
    mut v_inst_1332_: *mut leanh::LeanObject,
    mut v_it_1333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1339_: u8 = 0;
    let mut v_val_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1355_: u8 = 0;
    let mut v_unused_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1357_: u8 = 0;
    let mut v_unused_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1334_ = leanh::lean_ctor_get(v_it_1333_, 0);
                leanh::lean_inc(v_next_1334_);
                if leanh::lean_obj_tag(v_next_1334_) == 0 {
                    leanh::lean_dec_ref(v_it_1333_);
                    leanh::lean_dec_ref(v_inst_1332_);
                    leanh::lean_dec_ref(v_inst_1330_);
                    v___x_1335_ = leanh::lean_box(2);
                    return v___x_1335_;
                } else {
                    v_upperBound_1336_ = leanh::lean_ctor_get(v_it_1333_, 1);
                    v_isSharedCheck_1357_ = (!leanh::lean_is_exclusive(v_it_1333_)) as u8;
                    if v_isSharedCheck_1357_ == 0 {
                        v_unused_1358_ = leanh::lean_ctor_get(v_it_1333_, 0);
                        leanh::lean_dec(v_unused_1358_);
                        v___x_1338_ = v_it_1333_;
                        v_isShared_1339_ = v_isSharedCheck_1357_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_upperBound_1336_);
                        leanh::lean_dec(v_it_1333_);
                        v___x_1338_ = leanh::lean_box(0);
                        v_isShared_1339_ = v_isSharedCheck_1357_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1340_ = leanh::lean_ctor_get(v_next_1334_, 0);
                leanh::lean_inc_n(v_val_1340_, 2);
                leanh::lean_dec_ref_known(v_next_1334_, 1);
                leanh::lean_inc(v_upperBound_1336_);
                v___x_1341_ =
                    leanh::lean_apply_2(v_inst_1332_, v_val_1340_, v_upperBound_1336_);
                v___x_1342_ = (leanh::lean_unbox(v___x_1341_) as u8);
                if v___x_1342_ == 0 {
                    leanh::lean_dec(v_val_1340_);
                    leanh::lean_del_object(v___x_1338_);
                    leanh::lean_dec(v_upperBound_1336_);
                    leanh::lean_dec_ref(v_inst_1330_);
                    v___x_1343_ = leanh::lean_box(2);
                    return v___x_1343_;
                } else {
                    v_succ_x3f_1344_ = leanh::lean_ctor_get(v_inst_1330_, 0);
                    v_isSharedCheck_1355_ = (!leanh::lean_is_exclusive(v_inst_1330_)) as u8;
                    if v_isSharedCheck_1355_ == 0 {
                        v_unused_1356_ = leanh::lean_ctor_get(v_inst_1330_, 1);
                        leanh::lean_dec(v_unused_1356_);
                        v___x_1346_ = v_inst_1330_;
                        v_isShared_1347_ = v_isSharedCheck_1355_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_succ_x3f_1344_);
                        leanh::lean_dec(v_inst_1330_);
                        v___x_1346_ = leanh::lean_box(0);
                        v_isShared_1347_ = v_isSharedCheck_1355_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_val_1340_);
                v___x_1348_ = leanh::lean_apply_1(v_succ_x3f_1344_, v_val_1340_);
                if v_isShared_1339_ == 0 {
                    leanh::lean_ctor_set(v___x_1338_, 0, v___x_1348_);
                    v___x_1350_ = v___x_1338_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1354_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1348_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_upperBound_1336_);
                    v___x_1350_ = v_reuseFailAlloc_1354_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1347_ == 0 {
                    leanh::lean_ctor_set(v___x_1346_, 1, v_val_1340_);
                    leanh::lean_ctor_set(v___x_1346_, 0, v___x_1350_);
                    v___x_1352_ = v___x_1346_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1353_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_val_1340_);
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
    mut v_x_1359_: *mut leanh::LeanObject,
    mut v_h__1_1360_: *mut leanh::LeanObject,
    mut v_h__2_1361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1359_) == 0 {
        let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1361_);
        v___x_1362_ = leanh::lean_box(0);
        v___x_1363_ = leanh::lean_apply_1(v_h__1_1360_, v___x_1362_);
        return v___x_1363_;
    } else {
        let mut v_val_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1360_);
        v_val_1364_ = leanh::lean_ctor_get(v_x_1359_, 0);
        leanh::lean_inc(v_val_1364_);
        leanh::lean_dec_ref_known(v_x_1359_, 1);
        v___x_1365_ = leanh::lean_apply_1(v_h__2_1361_, v_val_1364_);
        return v___x_1365_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter(
    mut v_00_u03b1_1366_: *mut leanh::LeanObject,
    mut v_motive_1367_: *mut leanh::LeanObject,
    mut v_x_1368_: *mut leanh::LeanObject,
    mut v_h__1_1369_: *mut leanh::LeanObject,
    mut v_h__2_1370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1368_) == 0 {
        let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1370_);
        v___x_1371_ = leanh::lean_box(0);
        v___x_1372_ = leanh::lean_apply_1(v_h__1_1369_, v___x_1371_);
        return v___x_1372_;
    } else {
        let mut v_val_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1369_);
        v_val_1373_ = leanh::lean_ctor_get(v_x_1368_, 0);
        leanh::lean_inc(v_val_1373_);
        leanh::lean_dec_ref_known(v_x_1368_, 1);
        v___x_1374_ = leanh::lean_apply_1(v_h__2_1370_, v_val_1373_);
        return v___x_1374_;
    }
}
pub unsafe fn l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg___lam__0(
    mut v_inst_1375_: *mut leanh::LeanObject,
    mut v_inst_1376_: *mut leanh::LeanObject,
    mut v_it_1377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1383_: u8 = 0;
    let mut v_val_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: u8 = 0;
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1391_: u8 = 0;
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1399_: u8 = 0;
    let mut v_unused_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1401_: u8 = 0;
    let mut v_unused_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1378_ = leanh::lean_ctor_get(v_it_1377_, 0);
                leanh::lean_inc(v_next_1378_);
                if leanh::lean_obj_tag(v_next_1378_) == 0 {
                    leanh::lean_dec_ref(v_it_1377_);
                    leanh::lean_dec_ref(v_inst_1376_);
                    leanh::lean_dec_ref(v_inst_1375_);
                    v___x_1379_ = leanh::lean_box(2);
                    return v___x_1379_;
                } else {
                    v_upperBound_1380_ = leanh::lean_ctor_get(v_it_1377_, 1);
                    v_isSharedCheck_1401_ = (!leanh::lean_is_exclusive(v_it_1377_)) as u8;
                    if v_isSharedCheck_1401_ == 0 {
                        v_unused_1402_ = leanh::lean_ctor_get(v_it_1377_, 0);
                        leanh::lean_dec(v_unused_1402_);
                        v___x_1382_ = v_it_1377_;
                        v_isShared_1383_ = v_isSharedCheck_1401_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_upperBound_1380_);
                        leanh::lean_dec(v_it_1377_);
                        v___x_1382_ = leanh::lean_box(0);
                        v_isShared_1383_ = v_isSharedCheck_1401_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1384_ = leanh::lean_ctor_get(v_next_1378_, 0);
                leanh::lean_inc_n(v_val_1384_, 2);
                leanh::lean_dec_ref_known(v_next_1378_, 1);
                leanh::lean_inc(v_upperBound_1380_);
                v___x_1385_ =
                    leanh::lean_apply_2(v_inst_1375_, v_val_1384_, v_upperBound_1380_);
                v___x_1386_ = (leanh::lean_unbox(v___x_1385_) as u8);
                if v___x_1386_ == 0 {
                    leanh::lean_dec(v_val_1384_);
                    leanh::lean_del_object(v___x_1382_);
                    leanh::lean_dec(v_upperBound_1380_);
                    leanh::lean_dec_ref(v_inst_1376_);
                    v___x_1387_ = leanh::lean_box(2);
                    return v___x_1387_;
                } else {
                    v_succ_x3f_1388_ = leanh::lean_ctor_get(v_inst_1376_, 0);
                    v_isSharedCheck_1399_ = (!leanh::lean_is_exclusive(v_inst_1376_)) as u8;
                    if v_isSharedCheck_1399_ == 0 {
                        v_unused_1400_ = leanh::lean_ctor_get(v_inst_1376_, 1);
                        leanh::lean_dec(v_unused_1400_);
                        v___x_1390_ = v_inst_1376_;
                        v_isShared_1391_ = v_isSharedCheck_1399_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_succ_x3f_1388_);
                        leanh::lean_dec(v_inst_1376_);
                        v___x_1390_ = leanh::lean_box(0);
                        v_isShared_1391_ = v_isSharedCheck_1399_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_val_1384_);
                v___x_1392_ = leanh::lean_apply_1(v_succ_x3f_1388_, v_val_1384_);
                if v_isShared_1383_ == 0 {
                    leanh::lean_ctor_set(v___x_1382_, 0, v___x_1392_);
                    v___x_1394_ = v___x_1382_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1398_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1392_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_upperBound_1380_);
                    v___x_1394_ = v_reuseFailAlloc_1398_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1391_ == 0 {
                    leanh::lean_ctor_set(v___x_1390_, 1, v_val_1384_);
                    leanh::lean_ctor_set(v___x_1390_, 0, v___x_1394_);
                    v___x_1396_ = v___x_1390_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1397_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_val_1384_);
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
    mut v_inst_1403_: *mut leanh::LeanObject,
    mut v_inst_1404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1405_ = leanh::lean_alloc_closure(
        l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1405_, 0, v_inst_1404_);
    leanh::lean_closure_set(v___f_1405_, 1, v_inst_1403_);
    return v___f_1405_;
}
pub unsafe fn l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE(
    mut v_00_u03b1_1406_: *mut leanh::LeanObject,
    mut v_inst_1407_: *mut leanh::LeanObject,
    mut v_inst_1408_: *mut leanh::LeanObject,
    mut v_inst_1409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1410_ = leanh::lean_alloc_closure(
        l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1410_, 0, v_inst_1409_);
    leanh::lean_closure_set(v___f_1410_, 1, v_inst_1407_);
    return v___f_1410_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterStep_successor_match__1_splitter___redArg(
    mut v_x_1411_: *mut leanh::LeanObject,
    mut v_h__1_1412_: *mut leanh::LeanObject,
    mut v_h__2_1413_: *mut leanh::LeanObject,
    mut v_h__3_1414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1411_) {
        0 => {
            let mut v_it_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1414_);
            leanh::lean_dec(v_h__2_1413_);
            v_it_1415_ = leanh::lean_ctor_get(v_x_1411_, 0);
            leanh::lean_inc(v_it_1415_);
            v_out_1416_ = leanh::lean_ctor_get(v_x_1411_, 1);
            leanh::lean_inc(v_out_1416_);
            leanh::lean_dec_ref_known(v_x_1411_, 2);
            v___x_1417_ = leanh::lean_apply_2(v_h__1_1412_, v_it_1415_, v_out_1416_);
            return v___x_1417_;
        }
        1 => {
            let mut v_it_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1414_);
            leanh::lean_dec(v_h__1_1412_);
            v_it_1418_ = leanh::lean_ctor_get(v_x_1411_, 0);
            leanh::lean_inc(v_it_1418_);
            leanh::lean_dec_ref_known(v_x_1411_, 1);
            v___x_1419_ = leanh::lean_apply_1(v_h__2_1413_, v_it_1418_);
            return v___x_1419_;
        }
        _ => {
            let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1413_);
            leanh::lean_dec(v_h__1_1412_);
            v___x_1420_ = leanh::lean_box(0);
            v___x_1421_ = leanh::lean_apply_1(v_h__3_1414_, v___x_1420_);
            return v___x_1421_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterStep_successor_match__1_splitter(
    mut v_00_u03b1_1422_: *mut leanh::LeanObject,
    mut v_00_u03b2_1423_: *mut leanh::LeanObject,
    mut v_motive_1424_: *mut leanh::LeanObject,
    mut v_x_1425_: *mut leanh::LeanObject,
    mut v_h__1_1426_: *mut leanh::LeanObject,
    mut v_h__2_1427_: *mut leanh::LeanObject,
    mut v_h__3_1428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1425_) {
        0 => {
            let mut v_it_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1428_);
            leanh::lean_dec(v_h__2_1427_);
            v_it_1429_ = leanh::lean_ctor_get(v_x_1425_, 0);
            leanh::lean_inc(v_it_1429_);
            v_out_1430_ = leanh::lean_ctor_get(v_x_1425_, 1);
            leanh::lean_inc(v_out_1430_);
            leanh::lean_dec_ref_known(v_x_1425_, 2);
            v___x_1431_ = leanh::lean_apply_2(v_h__1_1426_, v_it_1429_, v_out_1430_);
            return v___x_1431_;
        }
        1 => {
            let mut v_it_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1428_);
            leanh::lean_dec(v_h__1_1426_);
            v_it_1432_ = leanh::lean_ctor_get(v_x_1425_, 0);
            leanh::lean_inc(v_it_1432_);
            leanh::lean_dec_ref_known(v_x_1425_, 1);
            v___x_1433_ = leanh::lean_apply_1(v_h__2_1427_, v_it_1432_);
            return v___x_1433_;
        }
        _ => {
            let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1427_);
            leanh::lean_dec(v_h__1_1426_);
            v___x_1434_ = leanh::lean_box(0);
            v___x_1435_ = leanh::lean_apply_1(v_h__3_1428_, v___x_1434_);
            return v___x_1435_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation(
    mut v_00_u03b1_1436_: *mut leanh::LeanObject,
    mut v_inst_1437_: *mut leanh::LeanObject,
    mut v_inst_1438_: *mut leanh::LeanObject,
    mut v_inst_1439_: *mut leanh::LeanObject,
    mut v_inst_1440_: *mut leanh::LeanObject,
    mut v_inst_1441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = leanh::lean_box(0);
    return v___x_1442_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___boxed(
    mut v_00_u03b1_1443_: *mut leanh::LeanObject,
    mut v_inst_1444_: *mut leanh::LeanObject,
    mut v_inst_1445_: *mut leanh::LeanObject,
    mut v_inst_1446_: *mut leanh::LeanObject,
    mut v_inst_1447_: *mut leanh::LeanObject,
    mut v_inst_1448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1449_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation(v_00_u03b1_1443_, v_inst_1444_, v_inst_1445_, v_inst_1446_, v_inst_1447_, v_inst_1448_);
    leanh::lean_dec_ref(v_inst_1446_);
    leanh::lean_dec_ref(v_inst_1444_);
    return v_res_1449_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation(
    mut v_00_u03b1_1450_: *mut leanh::LeanObject,
    mut v_inst_1451_: *mut leanh::LeanObject,
    mut v_inst_1452_: *mut leanh::LeanObject,
    mut v_inst_1453_: *mut leanh::LeanObject,
    mut v_inst_1454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1455_ = leanh::lean_box(0);
    return v___x_1455_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___boxed(
    mut v_00_u03b1_1456_: *mut leanh::LeanObject,
    mut v_inst_1457_: *mut leanh::LeanObject,
    mut v_inst_1458_: *mut leanh::LeanObject,
    mut v_inst_1459_: *mut leanh::LeanObject,
    mut v_inst_1460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1461_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation(v_00_u03b1_1456_, v_inst_1457_, v_inst_1458_, v_inst_1459_, v_inst_1460_);
    leanh::lean_dec_ref(v_inst_1459_);
    leanh::lean_dec_ref(v_inst_1457_);
    return v_res_1461_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorAccess_match__1_splitter___redArg(
    mut v_x_1462_: *mut leanh::LeanObject,
    mut v_h__1_1463_: *mut leanh::LeanObject,
    mut v_h__2_1464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1462_) == 0 {
        let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1464_);
        v___x_1465_ = leanh::lean_box(0);
        v___x_1466_ = leanh::lean_apply_1(v_h__1_1463_, v___x_1465_);
        return v___x_1466_;
    } else {
        let mut v_val_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1463_);
        v_val_1467_ = leanh::lean_ctor_get(v_x_1462_, 0);
        leanh::lean_inc(v_val_1467_);
        leanh::lean_dec_ref_known(v_x_1462_, 1);
        v___x_1468_ = leanh::lean_apply_1(v_h__2_1464_, v_val_1467_);
        return v___x_1468_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorAccess_match__1_splitter(
    mut v_00_u03b1_1469_: *mut leanh::LeanObject,
    mut v_motive_1470_: *mut leanh::LeanObject,
    mut v_x_1471_: *mut leanh::LeanObject,
    mut v_h__1_1472_: *mut leanh::LeanObject,
    mut v_h__2_1473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1471_) == 0 {
        let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1473_);
        v___x_1474_ = leanh::lean_box(0);
        v___x_1475_ = leanh::lean_apply_1(v_h__1_1472_, v___x_1474_);
        return v___x_1475_;
    } else {
        let mut v_val_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1472_);
        v_val_1476_ = leanh::lean_ctor_get(v_x_1471_, 0);
        leanh::lean_inc(v_val_1476_);
        leanh::lean_dec_ref_known(v_x_1471_, 1);
        v___x_1477_ = leanh::lean_apply_1(v_h__2_1473_, v_val_1476_);
        return v___x_1477_;
    }
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0(
    mut v_inst_1478_: *mut leanh::LeanObject,
    mut v_inst_1479_: *mut leanh::LeanObject,
    mut v_it_1480_: *mut leanh::LeanObject,
    mut v_n_1481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1487_: u8 = 0;
    let mut v_succ_x3f_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succMany_x3f_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v_val_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: u8 = 0;
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1507_: u8 = 0;
    let mut v_isSharedCheck_1508_: u8 = 0;
    let mut v_unused_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1482_ = leanh::lean_ctor_get(v_it_1480_, 0);
                leanh::lean_inc(v_next_1482_);
                if leanh::lean_obj_tag(v_next_1482_) == 0 {
                    leanh::lean_dec(v_n_1481_);
                    leanh::lean_dec_ref(v_it_1480_);
                    leanh::lean_dec_ref(v_inst_1479_);
                    leanh::lean_dec_ref(v_inst_1478_);
                    v___x_1483_ = leanh::lean_box(2);
                    return v___x_1483_;
                } else {
                    v_upperBound_1484_ = leanh::lean_ctor_get(v_it_1480_, 1);
                    v_isSharedCheck_1508_ = (!leanh::lean_is_exclusive(v_it_1480_)) as u8;
                    if v_isSharedCheck_1508_ == 0 {
                        v_unused_1509_ = leanh::lean_ctor_get(v_it_1480_, 0);
                        leanh::lean_dec(v_unused_1509_);
                        v___x_1486_ = v_it_1480_;
                        v_isShared_1487_ = v_isSharedCheck_1508_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_upperBound_1484_);
                        leanh::lean_dec(v_it_1480_);
                        v___x_1486_ = leanh::lean_box(0);
                        v_isShared_1487_ = v_isSharedCheck_1508_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_succ_x3f_1488_ = leanh::lean_ctor_get(v_inst_1478_, 0);
                v_succMany_x3f_1489_ = leanh::lean_ctor_get(v_inst_1478_, 1);
                v_isSharedCheck_1507_ = (!leanh::lean_is_exclusive(v_inst_1478_)) as u8;
                if v_isSharedCheck_1507_ == 0 {
                    v___x_1491_ = v_inst_1478_;
                    v_isShared_1492_ = v_isSharedCheck_1507_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_succMany_x3f_1489_);
                    leanh::lean_inc(v_succ_x3f_1488_);
                    leanh::lean_dec(v_inst_1478_);
                    v___x_1491_ = leanh::lean_box(0);
                    v_isShared_1492_ = v_isSharedCheck_1507_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_val_1493_ = leanh::lean_ctor_get(v_next_1482_, 0);
                leanh::lean_inc(v_val_1493_);
                leanh::lean_dec_ref_known(v_next_1482_, 1);
                v___x_1494_ =
                    leanh::lean_apply_2(v_succMany_x3f_1489_, v_n_1481_, v_val_1493_);
                if leanh::lean_obj_tag(v___x_1494_) == 0 {
                    leanh::lean_del_object(v___x_1491_);
                    leanh::lean_dec_ref(v_succ_x3f_1488_);
                    leanh::lean_del_object(v___x_1486_);
                    leanh::lean_dec(v_upperBound_1484_);
                    leanh::lean_dec_ref(v_inst_1479_);
                    v___x_1495_ = leanh::lean_box(2);
                    return v___x_1495_;
                } else {
                    v_val_1496_ = leanh::lean_ctor_get(v___x_1494_, 0);
                    leanh::lean_inc_n(v_val_1496_, 2);
                    leanh::lean_dec_ref_known(v___x_1494_, 1);
                    leanh::lean_inc(v_upperBound_1484_);
                    v___x_1497_ =
                        leanh::lean_apply_2(v_inst_1479_, v_val_1496_, v_upperBound_1484_);
                    v___x_1498_ = (leanh::lean_unbox(v___x_1497_) as u8);
                    if v___x_1498_ == 0 {
                        leanh::lean_dec(v_val_1496_);
                        leanh::lean_del_object(v___x_1491_);
                        leanh::lean_dec_ref(v_succ_x3f_1488_);
                        leanh::lean_del_object(v___x_1486_);
                        leanh::lean_dec(v_upperBound_1484_);
                        v___x_1499_ = leanh::lean_box(2);
                        return v___x_1499_;
                    } else {
                        leanh::lean_inc(v_val_1496_);
                        v___x_1500_ = leanh::lean_apply_1(v_succ_x3f_1488_, v_val_1496_);
                        if v_isShared_1487_ == 0 {
                            leanh::lean_ctor_set(v___x_1486_, 0, v___x_1500_);
                            v___x_1502_ = v___x_1486_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1506_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1500_);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1506_,
                                1,
                                v_upperBound_1484_,
                            );
                            v___x_1502_ = v_reuseFailAlloc_1506_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_1492_ == 0 {
                    leanh::lean_ctor_set(v___x_1491_, 1, v_val_1496_);
                    leanh::lean_ctor_set(v___x_1491_, 0, v___x_1502_);
                    v___x_1504_ = v___x_1491_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1505_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_val_1496_);
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
    mut v_inst_1510_: *mut leanh::LeanObject,
    mut v_inst_1511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1512_ = leanh::lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1512_, 0, v_inst_1510_);
    leanh::lean_closure_set(v___f_1512_, 1, v_inst_1511_);
    return v___f_1512_;
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorAccess(
    mut v_00_u03b1_1513_: *mut leanh::LeanObject,
    mut v_inst_1514_: *mut leanh::LeanObject,
    mut v_inst_1515_: *mut leanh::LeanObject,
    mut v_inst_1516_: *mut leanh::LeanObject,
    mut v_inst_1517_: *mut leanh::LeanObject,
    mut v_inst_1518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1519_ = leanh::lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1519_, 0, v_inst_1514_);
    leanh::lean_closure_set(v___f_1519_, 1, v_inst_1516_);
    return v___f_1519_;
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0(
    mut v_toApplicative_1520_: *mut leanh::LeanObject,
    mut v_inst_1521_: *mut leanh::LeanObject,
    mut v_next_1522_: *mut leanh::LeanObject,
    mut v_G_1523_: *mut leanh::LeanObject,
    mut v_____do__lift_1524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1524_) == 0 {
        let mut v_a_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_G_1523_);
        leanh::lean_dec(v_next_1522_);
        leanh::lean_dec_ref(v_inst_1521_);
        v_a_1525_ = leanh::lean_ctor_get(v_____do__lift_1524_, 0);
        leanh::lean_inc(v_a_1525_);
        leanh::lean_dec_ref_known(v_____do__lift_1524_, 1);
        v_toPure_1526_ = leanh::lean_ctor_get(v_toApplicative_1520_, 1);
        leanh::lean_inc(v_toPure_1526_);
        leanh::lean_dec_ref(v_toApplicative_1520_);
        v___x_1527_ =
            leanh::lean_apply_2(v_toPure_1526_, leanh::lean_box(0), v_a_1525_);
        return v___x_1527_;
    } else {
        let mut v_a_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_succ_x3f_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1528_ = leanh::lean_ctor_get(v_____do__lift_1524_, 0);
        leanh::lean_inc(v_a_1528_);
        leanh::lean_dec_ref_known(v_____do__lift_1524_, 1);
        v_succ_x3f_1529_ = leanh::lean_ctor_get(v_inst_1521_, 0);
        leanh::lean_inc_ref(v_succ_x3f_1529_);
        leanh::lean_dec_ref(v_inst_1521_);
        v___x_1530_ = leanh::lean_apply_1(v_succ_x3f_1529_, v_next_1522_);
        if leanh::lean_obj_tag(v___x_1530_) == 0 {
            let mut v_toPure_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_G_1523_);
            v_toPure_1531_ = leanh::lean_ctor_get(v_toApplicative_1520_, 1);
            leanh::lean_inc(v_toPure_1531_);
            leanh::lean_dec_ref(v_toApplicative_1520_);
            v___x_1532_ =
                leanh::lean_apply_2(v_toPure_1531_, leanh::lean_box(0), v_a_1528_);
            return v___x_1532_;
        } else {
            let mut v_val_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_toApplicative_1520_);
            v_val_1533_ = leanh::lean_ctor_get(v___x_1530_, 0);
            leanh::lean_inc(v_val_1533_);
            leanh::lean_dec_ref_known(v___x_1530_, 1);
            v___x_1534_ = leanh::lean_apply_4(
                v_G_1523_,
                v_val_1533_,
                v_a_1528_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_1534_;
        }
    }
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1(
    mut v_inst_1535_: *mut leanh::LeanObject,
    mut v_upperBound_1536_: *mut leanh::LeanObject,
    mut v_inst_1537_: *mut leanh::LeanObject,
    mut v_inst_1538_: *mut leanh::LeanObject,
    mut v_f_1539_: *mut leanh::LeanObject,
    mut v_next_1540_: *mut leanh::LeanObject,
    mut v_acc_1541_: *mut leanh::LeanObject,
    mut v_h_1542_: *mut leanh::LeanObject,
    mut v_G_1543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: u8 = 0;
    leanh::lean_inc(v_next_1540_);
    v___x_1544_ = leanh::lean_apply_2(v_inst_1535_, v_next_1540_, v_upperBound_1536_);
    v___x_1545_ = (leanh::lean_unbox(v___x_1544_) as u8);
    if v___x_1545_ == 0 {
        let mut v_toApplicative_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_G_1543_);
        leanh::lean_dec(v_next_1540_);
        leanh::lean_dec(v_f_1539_);
        leanh::lean_dec_ref(v_inst_1538_);
        v_toApplicative_1546_ = leanh::lean_ctor_get(v_inst_1537_, 0);
        leanh::lean_inc_ref(v_toApplicative_1546_);
        leanh::lean_dec_ref(v_inst_1537_);
        v_toPure_1547_ = leanh::lean_ctor_get(v_toApplicative_1546_, 1);
        leanh::lean_inc(v_toPure_1547_);
        leanh::lean_dec_ref(v_toApplicative_1546_);
        v___x_1548_ =
            leanh::lean_apply_2(v_toPure_1547_, leanh::lean_box(0), v_acc_1541_);
        return v___x_1548_;
    } else {
        let mut v_toApplicative_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1549_ = leanh::lean_ctor_get(v_inst_1537_, 0);
        leanh::lean_inc_ref(v_toApplicative_1549_);
        v_toBind_1550_ = leanh::lean_ctor_get(v_inst_1537_, 1);
        leanh::lean_inc(v_toBind_1550_);
        leanh::lean_dec_ref(v_inst_1537_);
        leanh::lean_inc(v_next_1540_);
        v___f_1551_ = leanh::lean_alloc_closure(
            l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_1551_, 0, v_toApplicative_1549_);
        leanh::lean_closure_set(v___f_1551_, 1, v_inst_1538_);
        leanh::lean_closure_set(v___f_1551_, 2, v_next_1540_);
        leanh::lean_closure_set(v___f_1551_, 3, v_G_1543_);
        v___x_1552_ = leanh::lean_apply_4(
            v_f_1539_,
            v_next_1540_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_acc_1541_,
        );
        v___x_1553_ = leanh::lean_apply_4(
            v_toBind_1550_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1552_,
            v___f_1551_,
        );
        return v___x_1553_;
    }
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg(
    mut v_inst_1554_: *mut leanh::LeanObject,
    mut v_inst_1555_: *mut leanh::LeanObject,
    mut v_inst_1556_: *mut leanh::LeanObject,
    mut v_upperBound_1557_: *mut leanh::LeanObject,
    mut v_acc_1558_: *mut leanh::LeanObject,
    mut v_next_1559_: *mut leanh::LeanObject,
    mut v_f_1560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1561_ = leanh::lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1 as *mut core::ffi::c_void,
        9,
        5,
    );
    leanh::lean_closure_set(v___f_1561_, 0, v_inst_1555_);
    leanh::lean_closure_set(v___f_1561_, 1, v_upperBound_1557_);
    leanh::lean_closure_set(v___f_1561_, 2, v_inst_1556_);
    leanh::lean_closure_set(v___f_1561_, 3, v_inst_1554_);
    leanh::lean_closure_set(v___f_1561_, 4, v_f_1560_);
    v___x_1562_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1561_,
        v_next_1559_,
        v_acc_1558_,
        leanh::lean_box(0),
    );
    return v___x_1562_;
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop_loop(
    mut v_00_u03b1_1563_: *mut leanh::LeanObject,
    mut v_inst_1564_: *mut leanh::LeanObject,
    mut v_inst_1565_: *mut leanh::LeanObject,
    mut v_inst_1566_: *mut leanh::LeanObject,
    mut v_inst_1567_: *mut leanh::LeanObject,
    mut v_inst_1568_: *mut leanh::LeanObject,
    mut v_n_1569_: *mut leanh::LeanObject,
    mut v_inst_1570_: *mut leanh::LeanObject,
    mut v_00_u03b3_1571_: *mut leanh::LeanObject,
    mut v_Pl_1572_: *mut leanh::LeanObject,
    mut v_LargeEnough_1573_: *mut leanh::LeanObject,
    mut v_hl_1574_: *mut leanh::LeanObject,
    mut v_upperBound_1575_: *mut leanh::LeanObject,
    mut v_acc_1576_: *mut leanh::LeanObject,
    mut v_next_1577_: *mut leanh::LeanObject,
    mut v_h_1578_: *mut leanh::LeanObject,
    mut v_f_1579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1580_ = leanh::lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1 as *mut core::ffi::c_void,
        9,
        5,
    );
    leanh::lean_closure_set(v___f_1580_, 0, v_inst_1566_);
    leanh::lean_closure_set(v___f_1580_, 1, v_upperBound_1575_);
    leanh::lean_closure_set(v___f_1580_, 2, v_inst_1570_);
    leanh::lean_closure_set(v___f_1580_, 3, v_inst_1564_);
    leanh::lean_closure_set(v___f_1580_, 4, v_f_1579_);
    v___x_1581_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1580_,
        v_next_1577_,
        v_acc_1576_,
        leanh::lean_box(0),
    );
    return v___x_1581_;
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop_loop___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_00_u03b1_1582_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_inst_1583_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_inst_1584_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_1585_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_inst_1586_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_inst_1587_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_n_1588_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_inst_1589_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_00_u03b3_1590_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_Pl_1591_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_LargeEnough_1592_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_hl_1593_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_upperBound_1594_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_acc_1595_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_next_1596_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_h_1597_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_f_1598_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_toPure_1600_: *mut leanh::LeanObject,
    mut v_inst_1601_: *mut leanh::LeanObject,
    mut v_next_1602_: *mut leanh::LeanObject,
    mut v_G_1603_: *mut leanh::LeanObject,
    mut v_____do__lift_1604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1604_) == 0 {
        let mut v_a_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_G_1603_);
        leanh::lean_dec(v_next_1602_);
        leanh::lean_dec_ref(v_inst_1601_);
        v_a_1605_ = leanh::lean_ctor_get(v_____do__lift_1604_, 0);
        leanh::lean_inc(v_a_1605_);
        leanh::lean_dec_ref_known(v_____do__lift_1604_, 1);
        v___x_1606_ =
            leanh::lean_apply_2(v_toPure_1600_, leanh::lean_box(0), v_a_1605_);
        return v___x_1606_;
    } else {
        let mut v_a_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_succ_x3f_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1607_ = leanh::lean_ctor_get(v_____do__lift_1604_, 0);
        leanh::lean_inc(v_a_1607_);
        leanh::lean_dec_ref_known(v_____do__lift_1604_, 1);
        v_succ_x3f_1608_ = leanh::lean_ctor_get(v_inst_1601_, 0);
        leanh::lean_inc_ref(v_succ_x3f_1608_);
        leanh::lean_dec_ref(v_inst_1601_);
        v___x_1609_ = leanh::lean_apply_1(v_succ_x3f_1608_, v_next_1602_);
        if leanh::lean_obj_tag(v___x_1609_) == 0 {
            let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_G_1603_);
            v___x_1610_ =
                leanh::lean_apply_2(v_toPure_1600_, leanh::lean_box(0), v_a_1607_);
            return v___x_1610_;
        } else {
            let mut v_val_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toPure_1600_);
            v_val_1611_ = leanh::lean_ctor_get(v___x_1609_, 0);
            leanh::lean_inc(v_val_1611_);
            leanh::lean_dec_ref_known(v___x_1609_, 1);
            v___x_1612_ = leanh::lean_apply_4(
                v_G_1603_,
                v_val_1611_,
                v_a_1607_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_1612_;
        }
    }
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1(
    mut v_inst_1613_: *mut leanh::LeanObject,
    mut v_upperBound_1614_: *mut leanh::LeanObject,
    mut v_toPure_1615_: *mut leanh::LeanObject,
    mut v_inst_1616_: *mut leanh::LeanObject,
    mut v_f_1617_: *mut leanh::LeanObject,
    mut v_toBind_1618_: *mut leanh::LeanObject,
    mut v_next_1619_: *mut leanh::LeanObject,
    mut v_acc_1620_: *mut leanh::LeanObject,
    mut v_h_1621_: *mut leanh::LeanObject,
    mut v_G_1622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: u8 = 0;
    leanh::lean_inc(v_next_1619_);
    v___x_1623_ = leanh::lean_apply_2(v_inst_1613_, v_next_1619_, v_upperBound_1614_);
    v___x_1624_ = (leanh::lean_unbox(v___x_1623_) as u8);
    if v___x_1624_ == 0 {
        let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_G_1622_);
        leanh::lean_dec(v_next_1619_);
        leanh::lean_dec(v_toBind_1618_);
        leanh::lean_dec(v_f_1617_);
        leanh::lean_dec_ref(v_inst_1616_);
        v___x_1625_ =
            leanh::lean_apply_2(v_toPure_1615_, leanh::lean_box(0), v_acc_1620_);
        return v___x_1625_;
    } else {
        let mut v___f_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_next_1619_);
        v___f_1626_ = leanh::lean_alloc_closure(
            l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_1626_, 0, v_toPure_1615_);
        leanh::lean_closure_set(v___f_1626_, 1, v_inst_1616_);
        leanh::lean_closure_set(v___f_1626_, 2, v_next_1619_);
        leanh::lean_closure_set(v___f_1626_, 3, v_G_1622_);
        v___x_1627_ = leanh::lean_apply_3(
            v_f_1617_,
            v_next_1619_,
            leanh::lean_box(0),
            v_acc_1620_,
        );
        v___x_1628_ = leanh::lean_apply_4(
            v_toBind_1618_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1627_,
            v___f_1626_,
        );
        return v___x_1628_;
    }
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2(
    mut v_toPure_1629_: *mut leanh::LeanObject,
    mut v_inst_1630_: *mut leanh::LeanObject,
    mut v_inst_1631_: *mut leanh::LeanObject,
    mut v_toBind_1632_: *mut leanh::LeanObject,
    mut v_x_1633_: *mut leanh::LeanObject,
    mut v_00_u03b3_1634_: *mut leanh::LeanObject,
    mut v_Pl_1635_: *mut leanh::LeanObject,
    mut v_it_1636_: *mut leanh::LeanObject,
    mut v_init_1637_: *mut leanh::LeanObject,
    mut v_f_1638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_next_1639_ = leanh::lean_ctor_get(v_it_1636_, 0);
    leanh::lean_inc(v_next_1639_);
    if leanh::lean_obj_tag(v_next_1639_) == 0 {
        let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_1638_);
        leanh::lean_dec_ref(v_it_1636_);
        leanh::lean_dec(v_toBind_1632_);
        leanh::lean_dec_ref(v_inst_1631_);
        leanh::lean_dec_ref(v_inst_1630_);
        v___x_1640_ =
            leanh::lean_apply_2(v_toPure_1629_, leanh::lean_box(0), v_init_1637_);
        return v___x_1640_;
    } else {
        let mut v_upperBound_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_upperBound_1641_ = leanh::lean_ctor_get(v_it_1636_, 1);
        leanh::lean_inc(v_upperBound_1641_);
        leanh::lean_dec_ref(v_it_1636_);
        v_val_1642_ = leanh::lean_ctor_get(v_next_1639_, 0);
        leanh::lean_inc(v_val_1642_);
        leanh::lean_dec_ref_known(v_next_1639_, 1);
        v___f_1643_ = leanh::lean_alloc_closure(
            l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
            10,
            6,
        );
        leanh::lean_closure_set(v___f_1643_, 0, v_inst_1630_);
        leanh::lean_closure_set(v___f_1643_, 1, v_upperBound_1641_);
        leanh::lean_closure_set(v___f_1643_, 2, v_toPure_1629_);
        leanh::lean_closure_set(v___f_1643_, 3, v_inst_1631_);
        leanh::lean_closure_set(v___f_1643_, 4, v_f_1638_);
        leanh::lean_closure_set(v___f_1643_, 5, v_toBind_1632_);
        v___x_1644_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_1643_,
            v_val_1642_,
            v_init_1637_,
            leanh::lean_box(0),
        );
        return v___x_1644_;
    }
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2___boxed(
    mut v_toPure_1645_: *mut leanh::LeanObject,
    mut v_inst_1646_: *mut leanh::LeanObject,
    mut v_inst_1647_: *mut leanh::LeanObject,
    mut v_toBind_1648_: *mut leanh::LeanObject,
    mut v_x_1649_: *mut leanh::LeanObject,
    mut v_00_u03b3_1650_: *mut leanh::LeanObject,
    mut v_Pl_1651_: *mut leanh::LeanObject,
    mut v_it_1652_: *mut leanh::LeanObject,
    mut v_init_1653_: *mut leanh::LeanObject,
    mut v_f_1654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_x_1649_);
    return v_res_1655_;
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop___redArg(
    mut v_inst_1656_: *mut leanh::LeanObject,
    mut v_inst_1657_: *mut leanh::LeanObject,
    mut v_inst_1658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1659_ = leanh::lean_ctor_get(v_inst_1658_, 0);
    leanh::lean_inc_ref(v_toApplicative_1659_);
    v_toBind_1660_ = leanh::lean_ctor_get(v_inst_1658_, 1);
    leanh::lean_inc(v_toBind_1660_);
    leanh::lean_dec_ref(v_inst_1658_);
    v_toPure_1661_ = leanh::lean_ctor_get(v_toApplicative_1659_, 1);
    leanh::lean_inc(v_toPure_1661_);
    leanh::lean_dec_ref(v_toApplicative_1659_);
    v___f_1662_ = leanh::lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2___boxed as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_1662_, 0, v_toPure_1661_);
    leanh::lean_closure_set(v___f_1662_, 1, v_inst_1657_);
    leanh::lean_closure_set(v___f_1662_, 2, v_inst_1656_);
    leanh::lean_closure_set(v___f_1662_, 3, v_toBind_1660_);
    return v___f_1662_;
}
pub unsafe fn l_Std_Rxc_Iterator_instIteratorLoop(
    mut v_00_u03b1_1663_: *mut leanh::LeanObject,
    mut v_inst_1664_: *mut leanh::LeanObject,
    mut v_inst_1665_: *mut leanh::LeanObject,
    mut v_inst_1666_: *mut leanh::LeanObject,
    mut v_inst_1667_: *mut leanh::LeanObject,
    mut v_inst_1668_: *mut leanh::LeanObject,
    mut v_n_1669_: *mut leanh::LeanObject,
    mut v_inst_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1671_ = leanh::lean_ctor_get(v_inst_1670_, 0);
    leanh::lean_inc_ref(v_toApplicative_1671_);
    v_toBind_1672_ = leanh::lean_ctor_get(v_inst_1670_, 1);
    leanh::lean_inc(v_toBind_1672_);
    leanh::lean_dec_ref(v_inst_1670_);
    v_toPure_1673_ = leanh::lean_ctor_get(v_toApplicative_1671_, 1);
    leanh::lean_inc(v_toPure_1673_);
    leanh::lean_dec_ref(v_toApplicative_1671_);
    v___f_1674_ = leanh::lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2___boxed as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_1674_, 0, v_toPure_1673_);
    leanh::lean_closure_set(v___f_1674_, 1, v_inst_1666_);
    leanh::lean_closure_set(v___f_1674_, 2, v_inst_1664_);
    leanh::lean_closure_set(v___f_1674_, 3, v_toBind_1672_);
    return v___f_1674_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter___redArg(
    mut v_____do__lift_1675_: *mut leanh::LeanObject,
    mut v_h__1_1676_: *mut leanh::LeanObject,
    mut v_h__2_1677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1675_) == 0 {
        let mut v_a_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1676_);
        v_a_1678_ = leanh::lean_ctor_get(v_____do__lift_1675_, 0);
        leanh::lean_inc(v_a_1678_);
        leanh::lean_dec_ref_known(v_____do__lift_1675_, 1);
        v___x_1679_ =
            leanh::lean_apply_2(v_h__2_1677_, v_a_1678_, leanh::lean_box(0));
        return v___x_1679_;
    } else {
        let mut v_a_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1677_);
        v_a_1680_ = leanh::lean_ctor_get(v_____do__lift_1675_, 0);
        leanh::lean_inc(v_a_1680_);
        leanh::lean_dec_ref_known(v_____do__lift_1675_, 1);
        v___x_1681_ =
            leanh::lean_apply_2(v_h__1_1676_, v_a_1680_, leanh::lean_box(0));
        return v___x_1681_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter(
    mut v_00_u03b1_1682_: *mut leanh::LeanObject,
    mut v_00_u03b3_1683_: *mut leanh::LeanObject,
    mut v_Pl_1684_: *mut leanh::LeanObject,
    mut v_acc_1685_: *mut leanh::LeanObject,
    mut v_next_1686_: *mut leanh::LeanObject,
    mut v_motive_1687_: *mut leanh::LeanObject,
    mut v_____do__lift_1688_: *mut leanh::LeanObject,
    mut v_h__1_1689_: *mut leanh::LeanObject,
    mut v_h__2_1690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1688_) == 0 {
        let mut v_a_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1689_);
        v_a_1691_ = leanh::lean_ctor_get(v_____do__lift_1688_, 0);
        leanh::lean_inc(v_a_1691_);
        leanh::lean_dec_ref_known(v_____do__lift_1688_, 1);
        v___x_1692_ =
            leanh::lean_apply_2(v_h__2_1690_, v_a_1691_, leanh::lean_box(0));
        return v___x_1692_;
    } else {
        let mut v_a_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1690_);
        v_a_1693_ = leanh::lean_ctor_get(v_____do__lift_1688_, 0);
        leanh::lean_inc(v_a_1693_);
        leanh::lean_dec_ref_known(v_____do__lift_1688_, 1);
        v___x_1694_ =
            leanh::lean_apply_2(v_h__1_1689_, v_a_1693_, leanh::lean_box(0));
        return v___x_1694_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter___boxed(
    mut v_00_u03b1_1695_: *mut leanh::LeanObject,
    mut v_00_u03b3_1696_: *mut leanh::LeanObject,
    mut v_Pl_1697_: *mut leanh::LeanObject,
    mut v_acc_1698_: *mut leanh::LeanObject,
    mut v_next_1699_: *mut leanh::LeanObject,
    mut v_motive_1700_: *mut leanh::LeanObject,
    mut v_____do__lift_1701_: *mut leanh::LeanObject,
    mut v_h__1_1702_: *mut leanh::LeanObject,
    mut v_h__2_1703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1704_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter(v_00_u03b1_1695_, v_00_u03b3_1696_, v_Pl_1697_, v_acc_1698_, v_next_1699_, v_motive_1700_, v_____do__lift_1701_, v_h__1_1702_, v_h__2_1703_);
    leanh::lean_dec(v_next_1699_);
    leanh::lean_dec(v_acc_1698_);
    return v_res_1704_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter___redArg(
    mut v_x_1705_: *mut leanh::LeanObject,
    mut v_h__1_1706_: *mut leanh::LeanObject,
    mut v_h__2_1707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1705_) == 0 {
        let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1706_);
        v___x_1708_ = leanh::lean_apply_1(v_h__2_1707_, leanh::lean_box(0));
        return v___x_1708_;
    } else {
        let mut v_val_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1707_);
        v_val_1709_ = leanh::lean_ctor_get(v_x_1705_, 0);
        leanh::lean_inc(v_val_1709_);
        leanh::lean_dec_ref_known(v_x_1705_, 1);
        v___x_1710_ =
            leanh::lean_apply_2(v_h__1_1706_, v_val_1709_, leanh::lean_box(0));
        return v___x_1710_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter(
    mut v_00_u03b1_1711_: *mut leanh::LeanObject,
    mut v_motive_1712_: *mut leanh::LeanObject,
    mut v_x_1713_: *mut leanh::LeanObject,
    mut v_h__1_1714_: *mut leanh::LeanObject,
    mut v_h__2_1715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1713_) == 0 {
        let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1714_);
        v___x_1716_ = leanh::lean_apply_1(v_h__2_1715_, leanh::lean_box(0));
        return v___x_1716_;
    } else {
        let mut v_val_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1715_);
        v_val_1717_ = leanh::lean_ctor_get(v_x_1713_, 0);
        leanh::lean_inc(v_val_1717_);
        leanh::lean_dec_ref_known(v_x_1713_, 1);
        v___x_1718_ =
            leanh::lean_apply_2(v_h__1_1714_, v_val_1717_, leanh::lean_box(0));
        return v___x_1718_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___redArg(
    mut v_____do__lift_1719_: *mut leanh::LeanObject,
    mut v_h__1_1720_: *mut leanh::LeanObject,
    mut v_h__2_1721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1719_) == 0 {
        let mut v_a_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1720_);
        v_a_1722_ = leanh::lean_ctor_get(v_____do__lift_1719_, 0);
        leanh::lean_inc(v_a_1722_);
        leanh::lean_dec_ref_known(v_____do__lift_1719_, 1);
        v___x_1723_ =
            leanh::lean_apply_2(v_h__2_1721_, v_a_1722_, leanh::lean_box(0));
        return v___x_1723_;
    } else {
        let mut v_a_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1721_);
        v_a_1724_ = leanh::lean_ctor_get(v_____do__lift_1719_, 0);
        leanh::lean_inc(v_a_1724_);
        leanh::lean_dec_ref_known(v_____do__lift_1719_, 1);
        v___x_1725_ =
            leanh::lean_apply_2(v_h__1_1720_, v_a_1724_, leanh::lean_box(0));
        return v___x_1725_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter(
    mut v_00_u03b1_1726_: *mut leanh::LeanObject,
    mut v_00_u03b3_1727_: *mut leanh::LeanObject,
    mut v_Pl_1728_: *mut leanh::LeanObject,
    mut v_next_1729_: *mut leanh::LeanObject,
    mut v_acc_1730_: *mut leanh::LeanObject,
    mut v_motive_1731_: *mut leanh::LeanObject,
    mut v_____do__lift_1732_: *mut leanh::LeanObject,
    mut v_h__1_1733_: *mut leanh::LeanObject,
    mut v_h__2_1734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1732_) == 0 {
        let mut v_a_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1733_);
        v_a_1735_ = leanh::lean_ctor_get(v_____do__lift_1732_, 0);
        leanh::lean_inc(v_a_1735_);
        leanh::lean_dec_ref_known(v_____do__lift_1732_, 1);
        v___x_1736_ =
            leanh::lean_apply_2(v_h__2_1734_, v_a_1735_, leanh::lean_box(0));
        return v___x_1736_;
    } else {
        let mut v_a_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1734_);
        v_a_1737_ = leanh::lean_ctor_get(v_____do__lift_1732_, 0);
        leanh::lean_inc(v_a_1737_);
        leanh::lean_dec_ref_known(v_____do__lift_1732_, 1);
        v___x_1738_ =
            leanh::lean_apply_2(v_h__1_1733_, v_a_1737_, leanh::lean_box(0));
        return v___x_1738_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___boxed(
    mut v_00_u03b1_1739_: *mut leanh::LeanObject,
    mut v_00_u03b3_1740_: *mut leanh::LeanObject,
    mut v_Pl_1741_: *mut leanh::LeanObject,
    mut v_next_1742_: *mut leanh::LeanObject,
    mut v_acc_1743_: *mut leanh::LeanObject,
    mut v_motive_1744_: *mut leanh::LeanObject,
    mut v_____do__lift_1745_: *mut leanh::LeanObject,
    mut v_h__1_1746_: *mut leanh::LeanObject,
    mut v_h__2_1747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1748_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter(v_00_u03b1_1739_, v_00_u03b3_1740_, v_Pl_1741_, v_next_1742_, v_acc_1743_, v_motive_1744_, v_____do__lift_1745_, v_h__1_1746_, v_h__2_1747_);
    leanh::lean_dec(v_acc_1743_);
    leanh::lean_dec(v_next_1742_);
    return v_res_1748_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_1749_: *mut leanh::LeanObject,
    mut v_h__1_1750_: *mut leanh::LeanObject,
    mut v_h__2_1751_: *mut leanh::LeanObject,
    mut v_h__3_1752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1749_) {
        0 => {
            let mut v_it_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1752_);
            leanh::lean_dec(v_h__2_1751_);
            v_it_1753_ = leanh::lean_ctor_get(v_x_1749_, 0);
            leanh::lean_inc(v_it_1753_);
            v_out_1754_ = leanh::lean_ctor_get(v_x_1749_, 1);
            leanh::lean_inc(v_out_1754_);
            leanh::lean_dec_ref_known(v_x_1749_, 2);
            v___x_1755_ = leanh::lean_apply_3(
                v_h__1_1750_,
                v_it_1753_,
                v_out_1754_,
                leanh::lean_box(0),
            );
            return v___x_1755_;
        }
        1 => {
            let mut v_it_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1752_);
            leanh::lean_dec(v_h__1_1750_);
            v_it_1756_ = leanh::lean_ctor_get(v_x_1749_, 0);
            leanh::lean_inc(v_it_1756_);
            leanh::lean_dec_ref_known(v_x_1749_, 1);
            v___x_1757_ =
                leanh::lean_apply_2(v_h__2_1751_, v_it_1756_, leanh::lean_box(0));
            return v___x_1757_;
        }
        _ => {
            let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1751_);
            leanh::lean_dec(v_h__1_1750_);
            v___x_1758_ = leanh::lean_apply_1(v_h__3_1752_, leanh::lean_box(0));
            return v___x_1758_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_1759_: *mut leanh::LeanObject,
    mut v_00_u03b2_1760_: *mut leanh::LeanObject,
    mut v_m_1761_: *mut leanh::LeanObject,
    mut v_inst_1762_: *mut leanh::LeanObject,
    mut v_it_1763_: *mut leanh::LeanObject,
    mut v_motive_1764_: *mut leanh::LeanObject,
    mut v_x_1765_: *mut leanh::LeanObject,
    mut v_h__1_1766_: *mut leanh::LeanObject,
    mut v_h__2_1767_: *mut leanh::LeanObject,
    mut v_h__3_1768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1765_) {
        0 => {
            let mut v_it_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1768_);
            leanh::lean_dec(v_h__2_1767_);
            v_it_1769_ = leanh::lean_ctor_get(v_x_1765_, 0);
            leanh::lean_inc(v_it_1769_);
            v_out_1770_ = leanh::lean_ctor_get(v_x_1765_, 1);
            leanh::lean_inc(v_out_1770_);
            leanh::lean_dec_ref_known(v_x_1765_, 2);
            v___x_1771_ = leanh::lean_apply_3(
                v_h__1_1766_,
                v_it_1769_,
                v_out_1770_,
                leanh::lean_box(0),
            );
            return v___x_1771_;
        }
        1 => {
            let mut v_it_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1768_);
            leanh::lean_dec(v_h__1_1766_);
            v_it_1772_ = leanh::lean_ctor_get(v_x_1765_, 0);
            leanh::lean_inc(v_it_1772_);
            leanh::lean_dec_ref_known(v_x_1765_, 1);
            v___x_1773_ =
                leanh::lean_apply_2(v_h__2_1767_, v_it_1772_, leanh::lean_box(0));
            return v___x_1773_;
        }
        _ => {
            let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1767_);
            leanh::lean_dec(v_h__1_1766_);
            v___x_1774_ = leanh::lean_apply_1(v_h__3_1768_, leanh::lean_box(0));
            return v___x_1774_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_1775_: *mut leanh::LeanObject,
    mut v_00_u03b2_1776_: *mut leanh::LeanObject,
    mut v_m_1777_: *mut leanh::LeanObject,
    mut v_inst_1778_: *mut leanh::LeanObject,
    mut v_it_1779_: *mut leanh::LeanObject,
    mut v_motive_1780_: *mut leanh::LeanObject,
    mut v_x_1781_: *mut leanh::LeanObject,
    mut v_h__1_1782_: *mut leanh::LeanObject,
    mut v_h__2_1783_: *mut leanh::LeanObject,
    mut v_h__3_1784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1785_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_1775_, v_00_u03b2_1776_, v_m_1777_, v_inst_1778_, v_it_1779_, v_motive_1780_, v_x_1781_, v_h__1_1782_, v_h__2_1783_, v_h__3_1784_);
    leanh::lean_dec(v_it_1779_);
    leanh::lean_dec(v_inst_1778_);
    return v_res_1785_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_1786_: *mut leanh::LeanObject,
    mut v_h__1_1787_: *mut leanh::LeanObject,
    mut v_h__2_1788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1786_) == 0 {
        let mut v_a_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1787_);
        v_a_1789_ = leanh::lean_ctor_get(v_____do__lift_1786_, 0);
        leanh::lean_inc(v_a_1789_);
        leanh::lean_dec_ref_known(v_____do__lift_1786_, 1);
        v___x_1790_ =
            leanh::lean_apply_2(v_h__2_1788_, v_a_1789_, leanh::lean_box(0));
        return v___x_1790_;
    } else {
        let mut v_a_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1788_);
        v_a_1791_ = leanh::lean_ctor_get(v_____do__lift_1786_, 0);
        leanh::lean_inc(v_a_1791_);
        leanh::lean_dec_ref_known(v_____do__lift_1786_, 1);
        v___x_1792_ =
            leanh::lean_apply_2(v_h__1_1787_, v_a_1791_, leanh::lean_box(0));
        return v___x_1792_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b2_1793_: *mut leanh::LeanObject,
    mut v_00_u03b3_1794_: *mut leanh::LeanObject,
    mut v_init_1795_: *mut leanh::LeanObject,
    mut v_PlausibleForInStep_1796_: *mut leanh::LeanObject,
    mut v_out_1797_: *mut leanh::LeanObject,
    mut v_motive_1798_: *mut leanh::LeanObject,
    mut v_____do__lift_1799_: *mut leanh::LeanObject,
    mut v_h__1_1800_: *mut leanh::LeanObject,
    mut v_h__2_1801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1799_) == 0 {
        let mut v_a_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1800_);
        v_a_1802_ = leanh::lean_ctor_get(v_____do__lift_1799_, 0);
        leanh::lean_inc(v_a_1802_);
        leanh::lean_dec_ref_known(v_____do__lift_1799_, 1);
        v___x_1803_ =
            leanh::lean_apply_2(v_h__2_1801_, v_a_1802_, leanh::lean_box(0));
        return v___x_1803_;
    } else {
        let mut v_a_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1801_);
        v_a_1804_ = leanh::lean_ctor_get(v_____do__lift_1799_, 0);
        leanh::lean_inc(v_a_1804_);
        leanh::lean_dec_ref_known(v_____do__lift_1799_, 1);
        v___x_1805_ =
            leanh::lean_apply_2(v_h__1_1800_, v_a_1804_, leanh::lean_box(0));
        return v___x_1805_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___boxed(
    mut v_00_u03b2_1806_: *mut leanh::LeanObject,
    mut v_00_u03b3_1807_: *mut leanh::LeanObject,
    mut v_init_1808_: *mut leanh::LeanObject,
    mut v_PlausibleForInStep_1809_: *mut leanh::LeanObject,
    mut v_out_1810_: *mut leanh::LeanObject,
    mut v_motive_1811_: *mut leanh::LeanObject,
    mut v_____do__lift_1812_: *mut leanh::LeanObject,
    mut v_h__1_1813_: *mut leanh::LeanObject,
    mut v_h__2_1814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1815_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(v_00_u03b2_1806_, v_00_u03b3_1807_, v_init_1808_, v_PlausibleForInStep_1809_, v_out_1810_, v_motive_1811_, v_____do__lift_1812_, v_h__1_1813_, v_h__2_1814_);
    leanh::lean_dec(v_out_1810_);
    leanh::lean_dec(v_init_1808_);
    return v_res_1815_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___redArg(
    mut v_it_1816_: *mut leanh::LeanObject,
    mut v_f_1817_: *mut leanh::LeanObject,
    mut v_h__1_1818_: *mut leanh::LeanObject,
    mut v_h__2_1819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_next_1820_ = leanh::lean_ctor_get(v_it_1816_, 0);
    if leanh::lean_obj_tag(v_next_1820_) == 0 {
        let mut v_upperBound_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1818_);
        v_upperBound_1821_ = leanh::lean_ctor_get(v_it_1816_, 1);
        leanh::lean_inc(v_upperBound_1821_);
        leanh::lean_dec_ref(v_it_1816_);
        v___x_1822_ = leanh::lean_apply_2(v_h__2_1819_, v_upperBound_1821_, v_f_1817_);
        return v___x_1822_;
    } else {
        let mut v_upperBound_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_next_1820_);
        leanh::lean_dec(v_h__2_1819_);
        v_upperBound_1823_ = leanh::lean_ctor_get(v_it_1816_, 1);
        leanh::lean_inc(v_upperBound_1823_);
        leanh::lean_dec_ref(v_it_1816_);
        v_val_1824_ = leanh::lean_ctor_get(v_next_1820_, 0);
        leanh::lean_inc(v_val_1824_);
        leanh::lean_dec_ref_known(v_next_1820_, 1);
        v___x_1825_ =
            leanh::lean_apply_3(v_h__1_1818_, v_val_1824_, v_upperBound_1823_, v_f_1817_);
        return v___x_1825_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter(
    mut v_00_u03b1_1826_: *mut leanh::LeanObject,
    mut v_inst_1827_: *mut leanh::LeanObject,
    mut v_inst_1828_: *mut leanh::LeanObject,
    mut v_inst_1829_: *mut leanh::LeanObject,
    mut v_n_1830_: *mut leanh::LeanObject,
    mut v_00_u03b3_1831_: *mut leanh::LeanObject,
    mut v_Pl_1832_: *mut leanh::LeanObject,
    mut v_motive_1833_: *mut leanh::LeanObject,
    mut v_it_1834_: *mut leanh::LeanObject,
    mut v_f_1835_: *mut leanh::LeanObject,
    mut v_h__1_1836_: *mut leanh::LeanObject,
    mut v_h__2_1837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_next_1838_ = leanh::lean_ctor_get(v_it_1834_, 0);
    if leanh::lean_obj_tag(v_next_1838_) == 0 {
        let mut v_upperBound_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1836_);
        v_upperBound_1839_ = leanh::lean_ctor_get(v_it_1834_, 1);
        leanh::lean_inc(v_upperBound_1839_);
        leanh::lean_dec_ref(v_it_1834_);
        v___x_1840_ = leanh::lean_apply_2(v_h__2_1837_, v_upperBound_1839_, v_f_1835_);
        return v___x_1840_;
    } else {
        let mut v_upperBound_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_next_1838_);
        leanh::lean_dec(v_h__2_1837_);
        v_upperBound_1841_ = leanh::lean_ctor_get(v_it_1834_, 1);
        leanh::lean_inc(v_upperBound_1841_);
        leanh::lean_dec_ref(v_it_1834_);
        v_val_1842_ = leanh::lean_ctor_get(v_next_1838_, 0);
        leanh::lean_inc(v_val_1842_);
        leanh::lean_dec_ref_known(v_next_1838_, 1);
        v___x_1843_ =
            leanh::lean_apply_3(v_h__1_1836_, v_val_1842_, v_upperBound_1841_, v_f_1835_);
        return v___x_1843_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___boxed(
    mut v_00_u03b1_1844_: *mut leanh::LeanObject,
    mut v_inst_1845_: *mut leanh::LeanObject,
    mut v_inst_1846_: *mut leanh::LeanObject,
    mut v_inst_1847_: *mut leanh::LeanObject,
    mut v_n_1848_: *mut leanh::LeanObject,
    mut v_00_u03b3_1849_: *mut leanh::LeanObject,
    mut v_Pl_1850_: *mut leanh::LeanObject,
    mut v_motive_1851_: *mut leanh::LeanObject,
    mut v_it_1852_: *mut leanh::LeanObject,
    mut v_f_1853_: *mut leanh::LeanObject,
    mut v_h__1_1854_: *mut leanh::LeanObject,
    mut v_h__2_1855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1856_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_1844_, v_inst_1845_, v_inst_1846_, v_inst_1847_, v_n_1848_, v_00_u03b3_1849_, v_Pl_1850_, v_motive_1851_, v_it_1852_, v_f_1853_, v_h__1_1854_, v_h__2_1855_);
    leanh::lean_dec_ref(v_inst_1847_);
    leanh::lean_dec_ref(v_inst_1845_);
    return v_res_1856_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(
    mut v_x_1857_: *mut leanh::LeanObject,
    mut v_h__1_1858_: *mut leanh::LeanObject,
    mut v_h__2_1859_: *mut leanh::LeanObject,
    mut v_h__3_1860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1857_) {
        0 => {
            let mut v_it_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1860_);
            leanh::lean_dec(v_h__2_1859_);
            v_it_1861_ = leanh::lean_ctor_get(v_x_1857_, 0);
            leanh::lean_inc(v_it_1861_);
            v_out_1862_ = leanh::lean_ctor_get(v_x_1857_, 1);
            leanh::lean_inc(v_out_1862_);
            leanh::lean_dec_ref_known(v_x_1857_, 2);
            v___x_1863_ = leanh::lean_apply_3(
                v_h__1_1858_,
                v_it_1861_,
                v_out_1862_,
                leanh::lean_box(0),
            );
            return v___x_1863_;
        }
        1 => {
            let mut v_it_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1860_);
            leanh::lean_dec(v_h__1_1858_);
            v_it_1864_ = leanh::lean_ctor_get(v_x_1857_, 0);
            leanh::lean_inc(v_it_1864_);
            leanh::lean_dec_ref_known(v_x_1857_, 1);
            v___x_1865_ =
                leanh::lean_apply_2(v_h__2_1859_, v_it_1864_, leanh::lean_box(0));
            return v___x_1865_;
        }
        _ => {
            let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1859_);
            leanh::lean_dec(v_h__1_1858_);
            v___x_1866_ = leanh::lean_apply_1(v_h__3_1860_, leanh::lean_box(0));
            return v___x_1866_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(
    mut v_m_1867_: *mut leanh::LeanObject,
    mut v_00_u03b1_1868_: *mut leanh::LeanObject,
    mut v_00_u03b2_1869_: *mut leanh::LeanObject,
    mut v_inst_1870_: *mut leanh::LeanObject,
    mut v_it_1871_: *mut leanh::LeanObject,
    mut v_motive_1872_: *mut leanh::LeanObject,
    mut v_x_1873_: *mut leanh::LeanObject,
    mut v_h__1_1874_: *mut leanh::LeanObject,
    mut v_h__2_1875_: *mut leanh::LeanObject,
    mut v_h__3_1876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1873_) {
        0 => {
            let mut v_it_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1876_);
            leanh::lean_dec(v_h__2_1875_);
            v_it_1877_ = leanh::lean_ctor_get(v_x_1873_, 0);
            leanh::lean_inc(v_it_1877_);
            v_out_1878_ = leanh::lean_ctor_get(v_x_1873_, 1);
            leanh::lean_inc(v_out_1878_);
            leanh::lean_dec_ref_known(v_x_1873_, 2);
            v___x_1879_ = leanh::lean_apply_3(
                v_h__1_1874_,
                v_it_1877_,
                v_out_1878_,
                leanh::lean_box(0),
            );
            return v___x_1879_;
        }
        1 => {
            let mut v_it_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1876_);
            leanh::lean_dec(v_h__1_1874_);
            v_it_1880_ = leanh::lean_ctor_get(v_x_1873_, 0);
            leanh::lean_inc(v_it_1880_);
            leanh::lean_dec_ref_known(v_x_1873_, 1);
            v___x_1881_ =
                leanh::lean_apply_2(v_h__2_1875_, v_it_1880_, leanh::lean_box(0));
            return v___x_1881_;
        }
        _ => {
            let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1875_);
            leanh::lean_dec(v_h__1_1874_);
            v___x_1882_ = leanh::lean_apply_1(v_h__3_1876_, leanh::lean_box(0));
            return v___x_1882_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(
    mut v_m_1883_: *mut leanh::LeanObject,
    mut v_00_u03b1_1884_: *mut leanh::LeanObject,
    mut v_00_u03b2_1885_: *mut leanh::LeanObject,
    mut v_inst_1886_: *mut leanh::LeanObject,
    mut v_it_1887_: *mut leanh::LeanObject,
    mut v_motive_1888_: *mut leanh::LeanObject,
    mut v_x_1889_: *mut leanh::LeanObject,
    mut v_h__1_1890_: *mut leanh::LeanObject,
    mut v_h__2_1891_: *mut leanh::LeanObject,
    mut v_h__3_1892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1893_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(v_m_1883_, v_00_u03b1_1884_, v_00_u03b2_1885_, v_inst_1886_, v_it_1887_, v_motive_1888_, v_x_1889_, v_h__1_1890_, v_h__2_1891_, v_h__3_1892_);
    leanh::lean_dec(v_it_1887_);
    leanh::lean_dec(v_inst_1886_);
    return v_res_1893_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(
    mut v_____do__lift_1894_: *mut leanh::LeanObject,
    mut v_h__1_1895_: *mut leanh::LeanObject,
    mut v_h__2_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1894_) == 0 {
        let mut v_a_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1895_);
        v_a_1897_ = leanh::lean_ctor_get(v_____do__lift_1894_, 0);
        leanh::lean_inc(v_a_1897_);
        leanh::lean_dec_ref_known(v_____do__lift_1894_, 1);
        v___x_1898_ =
            leanh::lean_apply_2(v_h__2_1896_, v_a_1897_, leanh::lean_box(0));
        return v___x_1898_;
    } else {
        let mut v_a_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1896_);
        v_a_1899_ = leanh::lean_ctor_get(v_____do__lift_1894_, 0);
        leanh::lean_inc(v_a_1899_);
        leanh::lean_dec_ref_known(v_____do__lift_1894_, 1);
        v___x_1900_ =
            leanh::lean_apply_2(v_h__1_1895_, v_a_1899_, leanh::lean_box(0));
        return v___x_1900_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(
    mut v_00_u03b2_1901_: *mut leanh::LeanObject,
    mut v_00_u03b3_1902_: *mut leanh::LeanObject,
    mut v_PlausibleForInStep_1903_: *mut leanh::LeanObject,
    mut v_acc_1904_: *mut leanh::LeanObject,
    mut v_out_1905_: *mut leanh::LeanObject,
    mut v_motive_1906_: *mut leanh::LeanObject,
    mut v_____do__lift_1907_: *mut leanh::LeanObject,
    mut v_h__1_1908_: *mut leanh::LeanObject,
    mut v_h__2_1909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1907_) == 0 {
        let mut v_a_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1908_);
        v_a_1910_ = leanh::lean_ctor_get(v_____do__lift_1907_, 0);
        leanh::lean_inc(v_a_1910_);
        leanh::lean_dec_ref_known(v_____do__lift_1907_, 1);
        v___x_1911_ =
            leanh::lean_apply_2(v_h__2_1909_, v_a_1910_, leanh::lean_box(0));
        return v___x_1911_;
    } else {
        let mut v_a_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1909_);
        v_a_1912_ = leanh::lean_ctor_get(v_____do__lift_1907_, 0);
        leanh::lean_inc(v_a_1912_);
        leanh::lean_dec_ref_known(v_____do__lift_1907_, 1);
        v___x_1913_ =
            leanh::lean_apply_2(v_h__1_1908_, v_a_1912_, leanh::lean_box(0));
        return v___x_1913_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(
    mut v_00_u03b2_1914_: *mut leanh::LeanObject,
    mut v_00_u03b3_1915_: *mut leanh::LeanObject,
    mut v_PlausibleForInStep_1916_: *mut leanh::LeanObject,
    mut v_acc_1917_: *mut leanh::LeanObject,
    mut v_out_1918_: *mut leanh::LeanObject,
    mut v_motive_1919_: *mut leanh::LeanObject,
    mut v_____do__lift_1920_: *mut leanh::LeanObject,
    mut v_h__1_1921_: *mut leanh::LeanObject,
    mut v_h__2_1922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1923_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(v_00_u03b2_1914_, v_00_u03b3_1915_, v_PlausibleForInStep_1916_, v_acc_1917_, v_out_1918_, v_motive_1919_, v_____do__lift_1920_, v_h__1_1921_, v_h__2_1922_);
    leanh::lean_dec(v_out_1918_);
    leanh::lean_dec(v_acc_1917_);
    return v_res_1923_;
}
pub unsafe fn l_Std_Rxo_Iterator_Monadic_step___redArg(
    mut v_inst_1924_: *mut leanh::LeanObject,
    mut v_inst_1925_: *mut leanh::LeanObject,
    mut v_it_1926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1932_: u8 = 0;
    let mut v_val_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1940_: u8 = 0;
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1948_: u8 = 0;
    let mut v_unused_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1950_: u8 = 0;
    let mut v_unused_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1927_ = leanh::lean_ctor_get(v_it_1926_, 0);
                leanh::lean_inc(v_next_1927_);
                if leanh::lean_obj_tag(v_next_1927_) == 0 {
                    leanh::lean_dec_ref(v_it_1926_);
                    leanh::lean_dec_ref(v_inst_1925_);
                    leanh::lean_dec_ref(v_inst_1924_);
                    v___x_1928_ = leanh::lean_box(2);
                    return v___x_1928_;
                } else {
                    v_upperBound_1929_ = leanh::lean_ctor_get(v_it_1926_, 1);
                    v_isSharedCheck_1950_ = (!leanh::lean_is_exclusive(v_it_1926_)) as u8;
                    if v_isSharedCheck_1950_ == 0 {
                        v_unused_1951_ = leanh::lean_ctor_get(v_it_1926_, 0);
                        leanh::lean_dec(v_unused_1951_);
                        v___x_1931_ = v_it_1926_;
                        v_isShared_1932_ = v_isSharedCheck_1950_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_upperBound_1929_);
                        leanh::lean_dec(v_it_1926_);
                        v___x_1931_ = leanh::lean_box(0);
                        v_isShared_1932_ = v_isSharedCheck_1950_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1933_ = leanh::lean_ctor_get(v_next_1927_, 0);
                leanh::lean_inc_n(v_val_1933_, 2);
                leanh::lean_dec_ref_known(v_next_1927_, 1);
                leanh::lean_inc(v_upperBound_1929_);
                v___x_1934_ =
                    leanh::lean_apply_2(v_inst_1925_, v_val_1933_, v_upperBound_1929_);
                v___x_1935_ = (leanh::lean_unbox(v___x_1934_) as u8);
                if v___x_1935_ == 0 {
                    leanh::lean_dec(v_val_1933_);
                    leanh::lean_del_object(v___x_1931_);
                    leanh::lean_dec(v_upperBound_1929_);
                    leanh::lean_dec_ref(v_inst_1924_);
                    v___x_1936_ = leanh::lean_box(2);
                    return v___x_1936_;
                } else {
                    v_succ_x3f_1937_ = leanh::lean_ctor_get(v_inst_1924_, 0);
                    v_isSharedCheck_1948_ = (!leanh::lean_is_exclusive(v_inst_1924_)) as u8;
                    if v_isSharedCheck_1948_ == 0 {
                        v_unused_1949_ = leanh::lean_ctor_get(v_inst_1924_, 1);
                        leanh::lean_dec(v_unused_1949_);
                        v___x_1939_ = v_inst_1924_;
                        v_isShared_1940_ = v_isSharedCheck_1948_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_succ_x3f_1937_);
                        leanh::lean_dec(v_inst_1924_);
                        v___x_1939_ = leanh::lean_box(0);
                        v_isShared_1940_ = v_isSharedCheck_1948_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_val_1933_);
                v___x_1941_ = leanh::lean_apply_1(v_succ_x3f_1937_, v_val_1933_);
                if v_isShared_1932_ == 0 {
                    leanh::lean_ctor_set(v___x_1931_, 0, v___x_1941_);
                    v___x_1943_ = v___x_1931_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1947_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_upperBound_1929_);
                    v___x_1943_ = v_reuseFailAlloc_1947_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1940_ == 0 {
                    leanh::lean_ctor_set(v___x_1939_, 1, v_val_1933_);
                    leanh::lean_ctor_set(v___x_1939_, 0, v___x_1943_);
                    v___x_1945_ = v___x_1939_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1946_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_val_1933_);
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
    mut v_00_u03b1_1952_: *mut leanh::LeanObject,
    mut v_inst_1953_: *mut leanh::LeanObject,
    mut v_inst_1954_: *mut leanh::LeanObject,
    mut v_inst_1955_: *mut leanh::LeanObject,
    mut v_it_1956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1962_: u8 = 0;
    let mut v_val_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1970_: u8 = 0;
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1978_: u8 = 0;
    let mut v_unused_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1980_: u8 = 0;
    let mut v_unused_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1957_ = leanh::lean_ctor_get(v_it_1956_, 0);
                leanh::lean_inc(v_next_1957_);
                if leanh::lean_obj_tag(v_next_1957_) == 0 {
                    leanh::lean_dec_ref(v_it_1956_);
                    leanh::lean_dec_ref(v_inst_1955_);
                    leanh::lean_dec_ref(v_inst_1953_);
                    v___x_1958_ = leanh::lean_box(2);
                    return v___x_1958_;
                } else {
                    v_upperBound_1959_ = leanh::lean_ctor_get(v_it_1956_, 1);
                    v_isSharedCheck_1980_ = (!leanh::lean_is_exclusive(v_it_1956_)) as u8;
                    if v_isSharedCheck_1980_ == 0 {
                        v_unused_1981_ = leanh::lean_ctor_get(v_it_1956_, 0);
                        leanh::lean_dec(v_unused_1981_);
                        v___x_1961_ = v_it_1956_;
                        v_isShared_1962_ = v_isSharedCheck_1980_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_upperBound_1959_);
                        leanh::lean_dec(v_it_1956_);
                        v___x_1961_ = leanh::lean_box(0);
                        v_isShared_1962_ = v_isSharedCheck_1980_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1963_ = leanh::lean_ctor_get(v_next_1957_, 0);
                leanh::lean_inc_n(v_val_1963_, 2);
                leanh::lean_dec_ref_known(v_next_1957_, 1);
                leanh::lean_inc(v_upperBound_1959_);
                v___x_1964_ =
                    leanh::lean_apply_2(v_inst_1955_, v_val_1963_, v_upperBound_1959_);
                v___x_1965_ = (leanh::lean_unbox(v___x_1964_) as u8);
                if v___x_1965_ == 0 {
                    leanh::lean_dec(v_val_1963_);
                    leanh::lean_del_object(v___x_1961_);
                    leanh::lean_dec(v_upperBound_1959_);
                    leanh::lean_dec_ref(v_inst_1953_);
                    v___x_1966_ = leanh::lean_box(2);
                    return v___x_1966_;
                } else {
                    v_succ_x3f_1967_ = leanh::lean_ctor_get(v_inst_1953_, 0);
                    v_isSharedCheck_1978_ = (!leanh::lean_is_exclusive(v_inst_1953_)) as u8;
                    if v_isSharedCheck_1978_ == 0 {
                        v_unused_1979_ = leanh::lean_ctor_get(v_inst_1953_, 1);
                        leanh::lean_dec(v_unused_1979_);
                        v___x_1969_ = v_inst_1953_;
                        v_isShared_1970_ = v_isSharedCheck_1978_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_succ_x3f_1967_);
                        leanh::lean_dec(v_inst_1953_);
                        v___x_1969_ = leanh::lean_box(0);
                        v_isShared_1970_ = v_isSharedCheck_1978_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_val_1963_);
                v___x_1971_ = leanh::lean_apply_1(v_succ_x3f_1967_, v_val_1963_);
                if v_isShared_1962_ == 0 {
                    leanh::lean_ctor_set(v___x_1961_, 0, v___x_1971_);
                    v___x_1973_ = v___x_1961_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1977_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1971_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_upperBound_1959_);
                    v___x_1973_ = v_reuseFailAlloc_1977_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1970_ == 0 {
                    leanh::lean_ctor_set(v___x_1969_, 1, v_val_1963_);
                    leanh::lean_ctor_set(v___x_1969_, 0, v___x_1973_);
                    v___x_1975_ = v___x_1969_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1976_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_val_1963_);
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
    mut v_inst_1982_: *mut leanh::LeanObject,
    mut v_inst_1983_: *mut leanh::LeanObject,
    mut v_it_1984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1990_: u8 = 0;
    let mut v_val_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: u8 = 0;
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1998_: u8 = 0;
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2006_: u8 = 0;
    let mut v_unused_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2008_: u8 = 0;
    let mut v_unused_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1985_ = leanh::lean_ctor_get(v_it_1984_, 0);
                leanh::lean_inc(v_next_1985_);
                if leanh::lean_obj_tag(v_next_1985_) == 0 {
                    leanh::lean_dec_ref(v_it_1984_);
                    leanh::lean_dec_ref(v_inst_1983_);
                    leanh::lean_dec_ref(v_inst_1982_);
                    v___x_1986_ = leanh::lean_box(2);
                    return v___x_1986_;
                } else {
                    v_upperBound_1987_ = leanh::lean_ctor_get(v_it_1984_, 1);
                    v_isSharedCheck_2008_ = (!leanh::lean_is_exclusive(v_it_1984_)) as u8;
                    if v_isSharedCheck_2008_ == 0 {
                        v_unused_2009_ = leanh::lean_ctor_get(v_it_1984_, 0);
                        leanh::lean_dec(v_unused_2009_);
                        v___x_1989_ = v_it_1984_;
                        v_isShared_1990_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_upperBound_1987_);
                        leanh::lean_dec(v_it_1984_);
                        v___x_1989_ = leanh::lean_box(0);
                        v_isShared_1990_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1991_ = leanh::lean_ctor_get(v_next_1985_, 0);
                leanh::lean_inc_n(v_val_1991_, 2);
                leanh::lean_dec_ref_known(v_next_1985_, 1);
                leanh::lean_inc(v_upperBound_1987_);
                v___x_1992_ =
                    leanh::lean_apply_2(v_inst_1983_, v_val_1991_, v_upperBound_1987_);
                v___x_1993_ = (leanh::lean_unbox(v___x_1992_) as u8);
                if v___x_1993_ == 0 {
                    leanh::lean_dec(v_val_1991_);
                    leanh::lean_del_object(v___x_1989_);
                    leanh::lean_dec(v_upperBound_1987_);
                    leanh::lean_dec_ref(v_inst_1982_);
                    v___x_1994_ = leanh::lean_box(2);
                    return v___x_1994_;
                } else {
                    v_succ_x3f_1995_ = leanh::lean_ctor_get(v_inst_1982_, 0);
                    v_isSharedCheck_2006_ = (!leanh::lean_is_exclusive(v_inst_1982_)) as u8;
                    if v_isSharedCheck_2006_ == 0 {
                        v_unused_2007_ = leanh::lean_ctor_get(v_inst_1982_, 1);
                        leanh::lean_dec(v_unused_2007_);
                        v___x_1997_ = v_inst_1982_;
                        v_isShared_1998_ = v_isSharedCheck_2006_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_succ_x3f_1995_);
                        leanh::lean_dec(v_inst_1982_);
                        v___x_1997_ = leanh::lean_box(0);
                        v_isShared_1998_ = v_isSharedCheck_2006_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_val_1991_);
                v___x_1999_ = leanh::lean_apply_1(v_succ_x3f_1995_, v_val_1991_);
                if v_isShared_1990_ == 0 {
                    leanh::lean_ctor_set(v___x_1989_, 0, v___x_1999_);
                    v___x_2001_ = v___x_1989_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2005_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1999_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_upperBound_1987_);
                    v___x_2001_ = v_reuseFailAlloc_2005_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1998_ == 0 {
                    leanh::lean_ctor_set(v___x_1997_, 1, v_val_1991_);
                    leanh::lean_ctor_set(v___x_1997_, 0, v___x_2001_);
                    v___x_2003_ = v___x_1997_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2004_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_val_1991_);
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
    mut v_00_u03b1_2010_: *mut leanh::LeanObject,
    mut v_inst_2011_: *mut leanh::LeanObject,
    mut v_inst_2012_: *mut leanh::LeanObject,
    mut v_inst_2013_: *mut leanh::LeanObject,
    mut v_it_2014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2020_: u8 = 0;
    let mut v_val_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u8 = 0;
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2036_: u8 = 0;
    let mut v_unused_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_unused_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_2015_ = leanh::lean_ctor_get(v_it_2014_, 0);
                leanh::lean_inc(v_next_2015_);
                if leanh::lean_obj_tag(v_next_2015_) == 0 {
                    leanh::lean_dec_ref(v_it_2014_);
                    leanh::lean_dec_ref(v_inst_2013_);
                    leanh::lean_dec_ref(v_inst_2011_);
                    v___x_2016_ = leanh::lean_box(2);
                    return v___x_2016_;
                } else {
                    v_upperBound_2017_ = leanh::lean_ctor_get(v_it_2014_, 1);
                    v_isSharedCheck_2038_ = (!leanh::lean_is_exclusive(v_it_2014_)) as u8;
                    if v_isSharedCheck_2038_ == 0 {
                        v_unused_2039_ = leanh::lean_ctor_get(v_it_2014_, 0);
                        leanh::lean_dec(v_unused_2039_);
                        v___x_2019_ = v_it_2014_;
                        v_isShared_2020_ = v_isSharedCheck_2038_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_upperBound_2017_);
                        leanh::lean_dec(v_it_2014_);
                        v___x_2019_ = leanh::lean_box(0);
                        v_isShared_2020_ = v_isSharedCheck_2038_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_2021_ = leanh::lean_ctor_get(v_next_2015_, 0);
                leanh::lean_inc_n(v_val_2021_, 2);
                leanh::lean_dec_ref_known(v_next_2015_, 1);
                leanh::lean_inc(v_upperBound_2017_);
                v___x_2022_ =
                    leanh::lean_apply_2(v_inst_2013_, v_val_2021_, v_upperBound_2017_);
                v___x_2023_ = (leanh::lean_unbox(v___x_2022_) as u8);
                if v___x_2023_ == 0 {
                    leanh::lean_dec(v_val_2021_);
                    leanh::lean_del_object(v___x_2019_);
                    leanh::lean_dec(v_upperBound_2017_);
                    leanh::lean_dec_ref(v_inst_2011_);
                    v___x_2024_ = leanh::lean_box(2);
                    return v___x_2024_;
                } else {
                    v_succ_x3f_2025_ = leanh::lean_ctor_get(v_inst_2011_, 0);
                    v_isSharedCheck_2036_ = (!leanh::lean_is_exclusive(v_inst_2011_)) as u8;
                    if v_isSharedCheck_2036_ == 0 {
                        v_unused_2037_ = leanh::lean_ctor_get(v_inst_2011_, 1);
                        leanh::lean_dec(v_unused_2037_);
                        v___x_2027_ = v_inst_2011_;
                        v_isShared_2028_ = v_isSharedCheck_2036_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_succ_x3f_2025_);
                        leanh::lean_dec(v_inst_2011_);
                        v___x_2027_ = leanh::lean_box(0);
                        v_isShared_2028_ = v_isSharedCheck_2036_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_val_2021_);
                v___x_2029_ = leanh::lean_apply_1(v_succ_x3f_2025_, v_val_2021_);
                if v_isShared_2020_ == 0 {
                    leanh::lean_ctor_set(v___x_2019_, 0, v___x_2029_);
                    v___x_2031_ = v___x_2019_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2035_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2029_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_upperBound_2017_);
                    v___x_2031_ = v_reuseFailAlloc_2035_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2028_ == 0 {
                    leanh::lean_ctor_set(v___x_2027_, 1, v_val_2021_);
                    leanh::lean_ctor_set(v___x_2027_, 0, v___x_2031_);
                    v___x_2033_ = v___x_2027_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2034_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_val_2021_);
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
    mut v_inst_2040_: *mut leanh::LeanObject,
    mut v_inst_2041_: *mut leanh::LeanObject,
    mut v_it_2042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v_val_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: u8 = 0;
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2056_: u8 = 0;
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2064_: u8 = 0;
    let mut v_unused_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2066_: u8 = 0;
    let mut v_unused_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_2043_ = leanh::lean_ctor_get(v_it_2042_, 0);
                leanh::lean_inc(v_next_2043_);
                if leanh::lean_obj_tag(v_next_2043_) == 0 {
                    leanh::lean_dec_ref(v_it_2042_);
                    leanh::lean_dec_ref(v_inst_2041_);
                    leanh::lean_dec_ref(v_inst_2040_);
                    v___x_2044_ = leanh::lean_box(2);
                    return v___x_2044_;
                } else {
                    v_upperBound_2045_ = leanh::lean_ctor_get(v_it_2042_, 1);
                    v_isSharedCheck_2066_ = (!leanh::lean_is_exclusive(v_it_2042_)) as u8;
                    if v_isSharedCheck_2066_ == 0 {
                        v_unused_2067_ = leanh::lean_ctor_get(v_it_2042_, 0);
                        leanh::lean_dec(v_unused_2067_);
                        v___x_2047_ = v_it_2042_;
                        v_isShared_2048_ = v_isSharedCheck_2066_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_upperBound_2045_);
                        leanh::lean_dec(v_it_2042_);
                        v___x_2047_ = leanh::lean_box(0);
                        v_isShared_2048_ = v_isSharedCheck_2066_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_2049_ = leanh::lean_ctor_get(v_next_2043_, 0);
                leanh::lean_inc_n(v_val_2049_, 2);
                leanh::lean_dec_ref_known(v_next_2043_, 1);
                leanh::lean_inc(v_upperBound_2045_);
                v___x_2050_ =
                    leanh::lean_apply_2(v_inst_2040_, v_val_2049_, v_upperBound_2045_);
                v___x_2051_ = (leanh::lean_unbox(v___x_2050_) as u8);
                if v___x_2051_ == 0 {
                    leanh::lean_dec(v_val_2049_);
                    leanh::lean_del_object(v___x_2047_);
                    leanh::lean_dec(v_upperBound_2045_);
                    leanh::lean_dec_ref(v_inst_2041_);
                    v___x_2052_ = leanh::lean_box(2);
                    return v___x_2052_;
                } else {
                    v_succ_x3f_2053_ = leanh::lean_ctor_get(v_inst_2041_, 0);
                    v_isSharedCheck_2064_ = (!leanh::lean_is_exclusive(v_inst_2041_)) as u8;
                    if v_isSharedCheck_2064_ == 0 {
                        v_unused_2065_ = leanh::lean_ctor_get(v_inst_2041_, 1);
                        leanh::lean_dec(v_unused_2065_);
                        v___x_2055_ = v_inst_2041_;
                        v_isShared_2056_ = v_isSharedCheck_2064_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_succ_x3f_2053_);
                        leanh::lean_dec(v_inst_2041_);
                        v___x_2055_ = leanh::lean_box(0);
                        v_isShared_2056_ = v_isSharedCheck_2064_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_val_2049_);
                v___x_2057_ = leanh::lean_apply_1(v_succ_x3f_2053_, v_val_2049_);
                if v_isShared_2048_ == 0 {
                    leanh::lean_ctor_set(v___x_2047_, 0, v___x_2057_);
                    v___x_2059_ = v___x_2047_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2063_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2057_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_upperBound_2045_);
                    v___x_2059_ = v_reuseFailAlloc_2063_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2056_ == 0 {
                    leanh::lean_ctor_set(v___x_2055_, 1, v_val_2049_);
                    leanh::lean_ctor_set(v___x_2055_, 0, v___x_2059_);
                    v___x_2061_ = v___x_2055_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2062_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_val_2049_);
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
    mut v_inst_2068_: *mut leanh::LeanObject,
    mut v_inst_2069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2070_ = leanh::lean_alloc_closure(
        l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2070_, 0, v_inst_2069_);
    leanh::lean_closure_set(v___f_2070_, 1, v_inst_2068_);
    return v___f_2070_;
}
pub unsafe fn l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT(
    mut v_00_u03b1_2071_: *mut leanh::LeanObject,
    mut v_inst_2072_: *mut leanh::LeanObject,
    mut v_inst_2073_: *mut leanh::LeanObject,
    mut v_inst_2074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2075_ = leanh::lean_alloc_closure(
        l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2075_, 0, v_inst_2074_);
    leanh::lean_closure_set(v___f_2075_, 1, v_inst_2072_);
    return v___f_2075_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation(
    mut v_00_u03b1_2076_: *mut leanh::LeanObject,
    mut v_inst_2077_: *mut leanh::LeanObject,
    mut v_inst_2078_: *mut leanh::LeanObject,
    mut v_inst_2079_: *mut leanh::LeanObject,
    mut v_inst_2080_: *mut leanh::LeanObject,
    mut v_inst_2081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2082_ = leanh::lean_box(0);
    return v___x_2082_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___boxed(
    mut v_00_u03b1_2083_: *mut leanh::LeanObject,
    mut v_inst_2084_: *mut leanh::LeanObject,
    mut v_inst_2085_: *mut leanh::LeanObject,
    mut v_inst_2086_: *mut leanh::LeanObject,
    mut v_inst_2087_: *mut leanh::LeanObject,
    mut v_inst_2088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2089_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation(v_00_u03b1_2083_, v_inst_2084_, v_inst_2085_, v_inst_2086_, v_inst_2087_, v_inst_2088_);
    leanh::lean_dec_ref(v_inst_2086_);
    leanh::lean_dec_ref(v_inst_2084_);
    return v_res_2089_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation(
    mut v_00_u03b1_2090_: *mut leanh::LeanObject,
    mut v_inst_2091_: *mut leanh::LeanObject,
    mut v_inst_2092_: *mut leanh::LeanObject,
    mut v_inst_2093_: *mut leanh::LeanObject,
    mut v_inst_2094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2095_ = leanh::lean_box(0);
    return v___x_2095_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___boxed(
    mut v_00_u03b1_2096_: *mut leanh::LeanObject,
    mut v_inst_2097_: *mut leanh::LeanObject,
    mut v_inst_2098_: *mut leanh::LeanObject,
    mut v_inst_2099_: *mut leanh::LeanObject,
    mut v_inst_2100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2101_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation(v_00_u03b1_2096_, v_inst_2097_, v_inst_2098_, v_inst_2099_, v_inst_2100_);
    leanh::lean_dec_ref(v_inst_2099_);
    leanh::lean_dec_ref(v_inst_2097_);
    return v_res_2101_;
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0(
    mut v_inst_2102_: *mut leanh::LeanObject,
    mut v_inst_2103_: *mut leanh::LeanObject,
    mut v_it_2104_: *mut leanh::LeanObject,
    mut v_n_2105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2111_: u8 = 0;
    let mut v_succ_x3f_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succMany_x3f_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2116_: u8 = 0;
    let mut v_val_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: u8 = 0;
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2131_: u8 = 0;
    let mut v_isSharedCheck_2132_: u8 = 0;
    let mut v_unused_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_2106_ = leanh::lean_ctor_get(v_it_2104_, 0);
                leanh::lean_inc(v_next_2106_);
                if leanh::lean_obj_tag(v_next_2106_) == 0 {
                    leanh::lean_dec(v_n_2105_);
                    leanh::lean_dec_ref(v_it_2104_);
                    leanh::lean_dec_ref(v_inst_2103_);
                    leanh::lean_dec_ref(v_inst_2102_);
                    v___x_2107_ = leanh::lean_box(2);
                    return v___x_2107_;
                } else {
                    v_upperBound_2108_ = leanh::lean_ctor_get(v_it_2104_, 1);
                    v_isSharedCheck_2132_ = (!leanh::lean_is_exclusive(v_it_2104_)) as u8;
                    if v_isSharedCheck_2132_ == 0 {
                        v_unused_2133_ = leanh::lean_ctor_get(v_it_2104_, 0);
                        leanh::lean_dec(v_unused_2133_);
                        v___x_2110_ = v_it_2104_;
                        v_isShared_2111_ = v_isSharedCheck_2132_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_upperBound_2108_);
                        leanh::lean_dec(v_it_2104_);
                        v___x_2110_ = leanh::lean_box(0);
                        v_isShared_2111_ = v_isSharedCheck_2132_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_succ_x3f_2112_ = leanh::lean_ctor_get(v_inst_2102_, 0);
                v_succMany_x3f_2113_ = leanh::lean_ctor_get(v_inst_2102_, 1);
                v_isSharedCheck_2131_ = (!leanh::lean_is_exclusive(v_inst_2102_)) as u8;
                if v_isSharedCheck_2131_ == 0 {
                    v___x_2115_ = v_inst_2102_;
                    v_isShared_2116_ = v_isSharedCheck_2131_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_succMany_x3f_2113_);
                    leanh::lean_inc(v_succ_x3f_2112_);
                    leanh::lean_dec(v_inst_2102_);
                    v___x_2115_ = leanh::lean_box(0);
                    v_isShared_2116_ = v_isSharedCheck_2131_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_val_2117_ = leanh::lean_ctor_get(v_next_2106_, 0);
                leanh::lean_inc(v_val_2117_);
                leanh::lean_dec_ref_known(v_next_2106_, 1);
                v___x_2118_ =
                    leanh::lean_apply_2(v_succMany_x3f_2113_, v_n_2105_, v_val_2117_);
                if leanh::lean_obj_tag(v___x_2118_) == 0 {
                    leanh::lean_del_object(v___x_2115_);
                    leanh::lean_dec_ref(v_succ_x3f_2112_);
                    leanh::lean_del_object(v___x_2110_);
                    leanh::lean_dec(v_upperBound_2108_);
                    leanh::lean_dec_ref(v_inst_2103_);
                    v___x_2119_ = leanh::lean_box(2);
                    return v___x_2119_;
                } else {
                    v_val_2120_ = leanh::lean_ctor_get(v___x_2118_, 0);
                    leanh::lean_inc_n(v_val_2120_, 2);
                    leanh::lean_dec_ref_known(v___x_2118_, 1);
                    leanh::lean_inc(v_upperBound_2108_);
                    v___x_2121_ =
                        leanh::lean_apply_2(v_inst_2103_, v_val_2120_, v_upperBound_2108_);
                    v___x_2122_ = (leanh::lean_unbox(v___x_2121_) as u8);
                    if v___x_2122_ == 0 {
                        leanh::lean_dec(v_val_2120_);
                        leanh::lean_del_object(v___x_2115_);
                        leanh::lean_dec_ref(v_succ_x3f_2112_);
                        leanh::lean_del_object(v___x_2110_);
                        leanh::lean_dec(v_upperBound_2108_);
                        v___x_2123_ = leanh::lean_box(2);
                        return v___x_2123_;
                    } else {
                        leanh::lean_inc(v_val_2120_);
                        v___x_2124_ = leanh::lean_apply_1(v_succ_x3f_2112_, v_val_2120_);
                        if v_isShared_2111_ == 0 {
                            leanh::lean_ctor_set(v___x_2110_, 0, v___x_2124_);
                            v___x_2126_ = v___x_2110_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2130_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2124_);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2130_,
                                1,
                                v_upperBound_2108_,
                            );
                            v___x_2126_ = v_reuseFailAlloc_2130_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_2116_ == 0 {
                    leanh::lean_ctor_set(v___x_2115_, 1, v_val_2120_);
                    leanh::lean_ctor_set(v___x_2115_, 0, v___x_2126_);
                    v___x_2128_ = v___x_2115_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2129_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_val_2120_);
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
    mut v_inst_2134_: *mut leanh::LeanObject,
    mut v_inst_2135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2136_ = leanh::lean_alloc_closure(
        l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2136_, 0, v_inst_2134_);
    leanh::lean_closure_set(v___f_2136_, 1, v_inst_2135_);
    return v___f_2136_;
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorAccess(
    mut v_00_u03b1_2137_: *mut leanh::LeanObject,
    mut v_inst_2138_: *mut leanh::LeanObject,
    mut v_inst_2139_: *mut leanh::LeanObject,
    mut v_inst_2140_: *mut leanh::LeanObject,
    mut v_inst_2141_: *mut leanh::LeanObject,
    mut v_inst_2142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2143_ = leanh::lean_alloc_closure(
        l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2143_, 0, v_inst_2138_);
    leanh::lean_closure_set(v___f_2143_, 1, v_inst_2140_);
    return v___f_2143_;
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorLoop_loop___redArg(
    mut v_inst_2144_: *mut leanh::LeanObject,
    mut v_inst_2145_: *mut leanh::LeanObject,
    mut v_inst_2146_: *mut leanh::LeanObject,
    mut v_upperBound_2147_: *mut leanh::LeanObject,
    mut v_acc_2148_: *mut leanh::LeanObject,
    mut v_next_2149_: *mut leanh::LeanObject,
    mut v_f_2150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2151_ = leanh::lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1 as *mut core::ffi::c_void,
        9,
        5,
    );
    leanh::lean_closure_set(v___f_2151_, 0, v_inst_2145_);
    leanh::lean_closure_set(v___f_2151_, 1, v_upperBound_2147_);
    leanh::lean_closure_set(v___f_2151_, 2, v_inst_2146_);
    leanh::lean_closure_set(v___f_2151_, 3, v_inst_2144_);
    leanh::lean_closure_set(v___f_2151_, 4, v_f_2150_);
    v___x_2152_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_2151_,
        v_next_2149_,
        v_acc_2148_,
        leanh::lean_box(0),
    );
    return v___x_2152_;
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorLoop_loop(
    mut v_00_u03b1_2153_: *mut leanh::LeanObject,
    mut v_inst_2154_: *mut leanh::LeanObject,
    mut v_inst_2155_: *mut leanh::LeanObject,
    mut v_inst_2156_: *mut leanh::LeanObject,
    mut v_inst_2157_: *mut leanh::LeanObject,
    mut v_n_2158_: *mut leanh::LeanObject,
    mut v_inst_2159_: *mut leanh::LeanObject,
    mut v_00_u03b3_2160_: *mut leanh::LeanObject,
    mut v_Pl_2161_: *mut leanh::LeanObject,
    mut v_LargeEnough_2162_: *mut leanh::LeanObject,
    mut v_hl_2163_: *mut leanh::LeanObject,
    mut v_upperBound_2164_: *mut leanh::LeanObject,
    mut v_acc_2165_: *mut leanh::LeanObject,
    mut v_next_2166_: *mut leanh::LeanObject,
    mut v_h_2167_: *mut leanh::LeanObject,
    mut v_f_2168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2169_ = leanh::lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1 as *mut core::ffi::c_void,
        9,
        5,
    );
    leanh::lean_closure_set(v___f_2169_, 0, v_inst_2156_);
    leanh::lean_closure_set(v___f_2169_, 1, v_upperBound_2164_);
    leanh::lean_closure_set(v___f_2169_, 2, v_inst_2159_);
    leanh::lean_closure_set(v___f_2169_, 3, v_inst_2154_);
    leanh::lean_closure_set(v___f_2169_, 4, v_f_2168_);
    v___x_2170_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_2169_,
        v_next_2166_,
        v_acc_2165_,
        leanh::lean_box(0),
    );
    return v___x_2170_;
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2(
    mut v_toPure_2171_: *mut leanh::LeanObject,
    mut v_inst_2172_: *mut leanh::LeanObject,
    mut v_inst_2173_: *mut leanh::LeanObject,
    mut v_toBind_2174_: *mut leanh::LeanObject,
    mut v_x_2175_: *mut leanh::LeanObject,
    mut v_00_u03b3_2176_: *mut leanh::LeanObject,
    mut v_Pl_2177_: *mut leanh::LeanObject,
    mut v_it_2178_: *mut leanh::LeanObject,
    mut v_init_2179_: *mut leanh::LeanObject,
    mut v_f_2180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_next_2181_ = leanh::lean_ctor_get(v_it_2178_, 0);
    leanh::lean_inc(v_next_2181_);
    if leanh::lean_obj_tag(v_next_2181_) == 0 {
        let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_2180_);
        leanh::lean_dec_ref(v_it_2178_);
        leanh::lean_dec(v_toBind_2174_);
        leanh::lean_dec_ref(v_inst_2173_);
        leanh::lean_dec_ref(v_inst_2172_);
        v___x_2182_ =
            leanh::lean_apply_2(v_toPure_2171_, leanh::lean_box(0), v_init_2179_);
        return v___x_2182_;
    } else {
        let mut v_upperBound_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_upperBound_2183_ = leanh::lean_ctor_get(v_it_2178_, 1);
        leanh::lean_inc(v_upperBound_2183_);
        leanh::lean_dec_ref(v_it_2178_);
        v_val_2184_ = leanh::lean_ctor_get(v_next_2181_, 0);
        leanh::lean_inc(v_val_2184_);
        leanh::lean_dec_ref_known(v_next_2181_, 1);
        v___f_2185_ = leanh::lean_alloc_closure(
            l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
            10,
            6,
        );
        leanh::lean_closure_set(v___f_2185_, 0, v_inst_2172_);
        leanh::lean_closure_set(v___f_2185_, 1, v_upperBound_2183_);
        leanh::lean_closure_set(v___f_2185_, 2, v_toPure_2171_);
        leanh::lean_closure_set(v___f_2185_, 3, v_inst_2173_);
        leanh::lean_closure_set(v___f_2185_, 4, v_f_2180_);
        leanh::lean_closure_set(v___f_2185_, 5, v_toBind_2174_);
        v___x_2186_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_2185_,
            v_val_2184_,
            v_init_2179_,
            leanh::lean_box(0),
        );
        return v___x_2186_;
    }
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed(
    mut v_toPure_2187_: *mut leanh::LeanObject,
    mut v_inst_2188_: *mut leanh::LeanObject,
    mut v_inst_2189_: *mut leanh::LeanObject,
    mut v_toBind_2190_: *mut leanh::LeanObject,
    mut v_x_2191_: *mut leanh::LeanObject,
    mut v_00_u03b3_2192_: *mut leanh::LeanObject,
    mut v_Pl_2193_: *mut leanh::LeanObject,
    mut v_it_2194_: *mut leanh::LeanObject,
    mut v_init_2195_: *mut leanh::LeanObject,
    mut v_f_2196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_x_2191_);
    return v_res_2197_;
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorLoop___redArg(
    mut v_inst_2198_: *mut leanh::LeanObject,
    mut v_inst_2199_: *mut leanh::LeanObject,
    mut v_inst_2200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2201_ = leanh::lean_ctor_get(v_inst_2200_, 0);
    leanh::lean_inc_ref(v_toApplicative_2201_);
    v_toBind_2202_ = leanh::lean_ctor_get(v_inst_2200_, 1);
    leanh::lean_inc(v_toBind_2202_);
    leanh::lean_dec_ref(v_inst_2200_);
    v_toPure_2203_ = leanh::lean_ctor_get(v_toApplicative_2201_, 1);
    leanh::lean_inc(v_toPure_2203_);
    leanh::lean_dec_ref(v_toApplicative_2201_);
    v___f_2204_ = leanh::lean_alloc_closure(
        l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_2204_, 0, v_toPure_2203_);
    leanh::lean_closure_set(v___f_2204_, 1, v_inst_2199_);
    leanh::lean_closure_set(v___f_2204_, 2, v_inst_2198_);
    leanh::lean_closure_set(v___f_2204_, 3, v_toBind_2202_);
    return v___f_2204_;
}
pub unsafe fn l_Std_Rxo_Iterator_instIteratorLoop(
    mut v_00_u03b1_2205_: *mut leanh::LeanObject,
    mut v_inst_2206_: *mut leanh::LeanObject,
    mut v_inst_2207_: *mut leanh::LeanObject,
    mut v_inst_2208_: *mut leanh::LeanObject,
    mut v_inst_2209_: *mut leanh::LeanObject,
    mut v_inst_2210_: *mut leanh::LeanObject,
    mut v_n_2211_: *mut leanh::LeanObject,
    mut v_inst_2212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2213_ = leanh::lean_ctor_get(v_inst_2212_, 0);
    leanh::lean_inc_ref(v_toApplicative_2213_);
    v_toBind_2214_ = leanh::lean_ctor_get(v_inst_2212_, 1);
    leanh::lean_inc(v_toBind_2214_);
    leanh::lean_dec_ref(v_inst_2212_);
    v_toPure_2215_ = leanh::lean_ctor_get(v_toApplicative_2213_, 1);
    leanh::lean_inc(v_toPure_2215_);
    leanh::lean_dec_ref(v_toApplicative_2213_);
    v___f_2216_ = leanh::lean_alloc_closure(
        l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_2216_, 0, v_toPure_2215_);
    leanh::lean_closure_set(v___f_2216_, 1, v_inst_2208_);
    leanh::lean_closure_set(v___f_2216_, 2, v_inst_2206_);
    leanh::lean_closure_set(v___f_2216_, 3, v_toBind_2214_);
    return v___f_2216_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___redArg(
    mut v_it_2217_: *mut leanh::LeanObject,
    mut v_f_2218_: *mut leanh::LeanObject,
    mut v_h__1_2219_: *mut leanh::LeanObject,
    mut v_h__2_2220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_next_2221_ = leanh::lean_ctor_get(v_it_2217_, 0);
    if leanh::lean_obj_tag(v_next_2221_) == 0 {
        let mut v_upperBound_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2219_);
        v_upperBound_2222_ = leanh::lean_ctor_get(v_it_2217_, 1);
        leanh::lean_inc(v_upperBound_2222_);
        leanh::lean_dec_ref(v_it_2217_);
        v___x_2223_ = leanh::lean_apply_2(v_h__2_2220_, v_upperBound_2222_, v_f_2218_);
        return v___x_2223_;
    } else {
        let mut v_upperBound_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_next_2221_);
        leanh::lean_dec(v_h__2_2220_);
        v_upperBound_2224_ = leanh::lean_ctor_get(v_it_2217_, 1);
        leanh::lean_inc(v_upperBound_2224_);
        leanh::lean_dec_ref(v_it_2217_);
        v_val_2225_ = leanh::lean_ctor_get(v_next_2221_, 0);
        leanh::lean_inc(v_val_2225_);
        leanh::lean_dec_ref_known(v_next_2221_, 1);
        v___x_2226_ =
            leanh::lean_apply_3(v_h__1_2219_, v_val_2225_, v_upperBound_2224_, v_f_2218_);
        return v___x_2226_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter(
    mut v_00_u03b1_2227_: *mut leanh::LeanObject,
    mut v_inst_2228_: *mut leanh::LeanObject,
    mut v_inst_2229_: *mut leanh::LeanObject,
    mut v_inst_2230_: *mut leanh::LeanObject,
    mut v_n_2231_: *mut leanh::LeanObject,
    mut v_00_u03b3_2232_: *mut leanh::LeanObject,
    mut v_Pl_2233_: *mut leanh::LeanObject,
    mut v_motive_2234_: *mut leanh::LeanObject,
    mut v_it_2235_: *mut leanh::LeanObject,
    mut v_f_2236_: *mut leanh::LeanObject,
    mut v_h__1_2237_: *mut leanh::LeanObject,
    mut v_h__2_2238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_next_2239_ = leanh::lean_ctor_get(v_it_2235_, 0);
    if leanh::lean_obj_tag(v_next_2239_) == 0 {
        let mut v_upperBound_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2237_);
        v_upperBound_2240_ = leanh::lean_ctor_get(v_it_2235_, 1);
        leanh::lean_inc(v_upperBound_2240_);
        leanh::lean_dec_ref(v_it_2235_);
        v___x_2241_ = leanh::lean_apply_2(v_h__2_2238_, v_upperBound_2240_, v_f_2236_);
        return v___x_2241_;
    } else {
        let mut v_upperBound_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_next_2239_);
        leanh::lean_dec(v_h__2_2238_);
        v_upperBound_2242_ = leanh::lean_ctor_get(v_it_2235_, 1);
        leanh::lean_inc(v_upperBound_2242_);
        leanh::lean_dec_ref(v_it_2235_);
        v_val_2243_ = leanh::lean_ctor_get(v_next_2239_, 0);
        leanh::lean_inc(v_val_2243_);
        leanh::lean_dec_ref_known(v_next_2239_, 1);
        v___x_2244_ =
            leanh::lean_apply_3(v_h__1_2237_, v_val_2243_, v_upperBound_2242_, v_f_2236_);
        return v___x_2244_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___boxed(
    mut v_00_u03b1_2245_: *mut leanh::LeanObject,
    mut v_inst_2246_: *mut leanh::LeanObject,
    mut v_inst_2247_: *mut leanh::LeanObject,
    mut v_inst_2248_: *mut leanh::LeanObject,
    mut v_n_2249_: *mut leanh::LeanObject,
    mut v_00_u03b3_2250_: *mut leanh::LeanObject,
    mut v_Pl_2251_: *mut leanh::LeanObject,
    mut v_motive_2252_: *mut leanh::LeanObject,
    mut v_it_2253_: *mut leanh::LeanObject,
    mut v_f_2254_: *mut leanh::LeanObject,
    mut v_h__1_2255_: *mut leanh::LeanObject,
    mut v_h__2_2256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2257_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_2245_, v_inst_2246_, v_inst_2247_, v_inst_2248_, v_n_2249_, v_00_u03b3_2250_, v_Pl_2251_, v_motive_2252_, v_it_2253_, v_f_2254_, v_h__1_2255_, v_h__2_2256_);
    leanh::lean_dec_ref(v_inst_2248_);
    leanh::lean_dec_ref(v_inst_2246_);
    return v_res_2257_;
}
pub unsafe fn l_Std_Rxi_Iterator_Monadic_step___redArg(
    mut v_inst_2258_: *mut leanh::LeanObject,
    mut v_it_2259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut v_unused_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_it_2259_) == 0 {
                    leanh::lean_dec_ref(v_inst_2258_);
                    v___x_2260_ = leanh::lean_box(2);
                    return v___x_2260_;
                } else {
                    v_val_2261_ = leanh::lean_ctor_get(v_it_2259_, 0);
                    leanh::lean_inc(v_val_2261_);
                    leanh::lean_dec_ref_known(v_it_2259_, 1);
                    v_succ_x3f_2262_ = leanh::lean_ctor_get(v_inst_2258_, 0);
                    v_isSharedCheck_2270_ = (!leanh::lean_is_exclusive(v_inst_2258_)) as u8;
                    if v_isSharedCheck_2270_ == 0 {
                        v_unused_2271_ = leanh::lean_ctor_get(v_inst_2258_, 1);
                        leanh::lean_dec(v_unused_2271_);
                        v___x_2264_ = v_inst_2258_;
                        v_isShared_2265_ = v_isSharedCheck_2270_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_succ_x3f_2262_);
                        leanh::lean_dec(v_inst_2258_);
                        v___x_2264_ = leanh::lean_box(0);
                        v_isShared_2265_ = v_isSharedCheck_2270_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_val_2261_);
                v___x_2266_ = leanh::lean_apply_1(v_succ_x3f_2262_, v_val_2261_);
                if v_isShared_2265_ == 0 {
                    leanh::lean_ctor_set(v___x_2264_, 1, v_val_2261_);
                    leanh::lean_ctor_set(v___x_2264_, 0, v___x_2266_);
                    v___x_2268_ = v___x_2264_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_val_2261_);
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
    mut v_00_u03b1_2272_: *mut leanh::LeanObject,
    mut v_inst_2273_: *mut leanh::LeanObject,
    mut v_it_2274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2280_: u8 = 0;
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2285_: u8 = 0;
    let mut v_unused_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_it_2274_) == 0 {
                    leanh::lean_dec_ref(v_inst_2273_);
                    v___x_2275_ = leanh::lean_box(2);
                    return v___x_2275_;
                } else {
                    v_val_2276_ = leanh::lean_ctor_get(v_it_2274_, 0);
                    leanh::lean_inc(v_val_2276_);
                    leanh::lean_dec_ref_known(v_it_2274_, 1);
                    v_succ_x3f_2277_ = leanh::lean_ctor_get(v_inst_2273_, 0);
                    v_isSharedCheck_2285_ = (!leanh::lean_is_exclusive(v_inst_2273_)) as u8;
                    if v_isSharedCheck_2285_ == 0 {
                        v_unused_2286_ = leanh::lean_ctor_get(v_inst_2273_, 1);
                        leanh::lean_dec(v_unused_2286_);
                        v___x_2279_ = v_inst_2273_;
                        v_isShared_2280_ = v_isSharedCheck_2285_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_succ_x3f_2277_);
                        leanh::lean_dec(v_inst_2273_);
                        v___x_2279_ = leanh::lean_box(0);
                        v_isShared_2280_ = v_isSharedCheck_2285_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_val_2276_);
                v___x_2281_ = leanh::lean_apply_1(v_succ_x3f_2277_, v_val_2276_);
                if v_isShared_2280_ == 0 {
                    leanh::lean_ctor_set(v___x_2279_, 1, v_val_2276_);
                    leanh::lean_ctor_set(v___x_2279_, 0, v___x_2281_);
                    v___x_2283_ = v___x_2279_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2284_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_val_2276_);
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
    mut v_inst_2287_: *mut leanh::LeanObject,
    mut v_it_2288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2294_: u8 = 0;
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut v_unused_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_it_2288_) == 0 {
                    leanh::lean_dec_ref(v_inst_2287_);
                    v___x_2289_ = leanh::lean_box(2);
                    return v___x_2289_;
                } else {
                    v_val_2290_ = leanh::lean_ctor_get(v_it_2288_, 0);
                    leanh::lean_inc(v_val_2290_);
                    leanh::lean_dec_ref_known(v_it_2288_, 1);
                    v_succ_x3f_2291_ = leanh::lean_ctor_get(v_inst_2287_, 0);
                    v_isSharedCheck_2299_ = (!leanh::lean_is_exclusive(v_inst_2287_)) as u8;
                    if v_isSharedCheck_2299_ == 0 {
                        v_unused_2300_ = leanh::lean_ctor_get(v_inst_2287_, 1);
                        leanh::lean_dec(v_unused_2300_);
                        v___x_2293_ = v_inst_2287_;
                        v_isShared_2294_ = v_isSharedCheck_2299_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_succ_x3f_2291_);
                        leanh::lean_dec(v_inst_2287_);
                        v___x_2293_ = leanh::lean_box(0);
                        v_isShared_2294_ = v_isSharedCheck_2299_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_val_2290_);
                v___x_2295_ = leanh::lean_apply_1(v_succ_x3f_2291_, v_val_2290_);
                if v_isShared_2294_ == 0 {
                    leanh::lean_ctor_set(v___x_2293_, 1, v_val_2290_);
                    leanh::lean_ctor_set(v___x_2293_, 0, v___x_2295_);
                    v___x_2297_ = v___x_2293_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2298_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_val_2290_);
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
    mut v_00_u03b1_2301_: *mut leanh::LeanObject,
    mut v_inst_2302_: *mut leanh::LeanObject,
    mut v_it_2303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2309_: u8 = 0;
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2314_: u8 = 0;
    let mut v_unused_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_it_2303_) == 0 {
                    leanh::lean_dec_ref(v_inst_2302_);
                    v___x_2304_ = leanh::lean_box(2);
                    return v___x_2304_;
                } else {
                    v_val_2305_ = leanh::lean_ctor_get(v_it_2303_, 0);
                    leanh::lean_inc(v_val_2305_);
                    leanh::lean_dec_ref_known(v_it_2303_, 1);
                    v_succ_x3f_2306_ = leanh::lean_ctor_get(v_inst_2302_, 0);
                    v_isSharedCheck_2314_ = (!leanh::lean_is_exclusive(v_inst_2302_)) as u8;
                    if v_isSharedCheck_2314_ == 0 {
                        v_unused_2315_ = leanh::lean_ctor_get(v_inst_2302_, 1);
                        leanh::lean_dec(v_unused_2315_);
                        v___x_2308_ = v_inst_2302_;
                        v_isShared_2309_ = v_isSharedCheck_2314_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_succ_x3f_2306_);
                        leanh::lean_dec(v_inst_2302_);
                        v___x_2308_ = leanh::lean_box(0);
                        v_isShared_2309_ = v_isSharedCheck_2314_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_val_2305_);
                v___x_2310_ = leanh::lean_apply_1(v_succ_x3f_2306_, v_val_2305_);
                if v_isShared_2309_ == 0 {
                    leanh::lean_ctor_set(v___x_2308_, 1, v_val_2305_);
                    leanh::lean_ctor_set(v___x_2308_, 0, v___x_2310_);
                    v___x_2312_ = v___x_2308_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2313_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_val_2305_);
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
    mut v_inst_2316_: *mut leanh::LeanObject,
    mut v_it_2317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2323_: u8 = 0;
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2328_: u8 = 0;
    let mut v_unused_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_it_2317_) == 0 {
                    leanh::lean_dec_ref(v_inst_2316_);
                    v___x_2318_ = leanh::lean_box(2);
                    return v___x_2318_;
                } else {
                    v_val_2319_ = leanh::lean_ctor_get(v_it_2317_, 0);
                    leanh::lean_inc(v_val_2319_);
                    leanh::lean_dec_ref_known(v_it_2317_, 1);
                    v_succ_x3f_2320_ = leanh::lean_ctor_get(v_inst_2316_, 0);
                    v_isSharedCheck_2328_ = (!leanh::lean_is_exclusive(v_inst_2316_)) as u8;
                    if v_isSharedCheck_2328_ == 0 {
                        v_unused_2329_ = leanh::lean_ctor_get(v_inst_2316_, 1);
                        leanh::lean_dec(v_unused_2329_);
                        v___x_2322_ = v_inst_2316_;
                        v_isShared_2323_ = v_isSharedCheck_2328_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_succ_x3f_2320_);
                        leanh::lean_dec(v_inst_2316_);
                        v___x_2322_ = leanh::lean_box(0);
                        v_isShared_2323_ = v_isSharedCheck_2328_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_val_2319_);
                v___x_2324_ = leanh::lean_apply_1(v_succ_x3f_2320_, v_val_2319_);
                if v_isShared_2323_ == 0 {
                    leanh::lean_ctor_set(v___x_2322_, 1, v_val_2319_);
                    leanh::lean_ctor_set(v___x_2322_, 0, v___x_2324_);
                    v___x_2326_ = v___x_2322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2327_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_val_2319_);
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
    mut v_inst_2330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2331_ = leanh::lean_alloc_closure(
        l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2331_, 0, v_inst_2330_);
    return v___f_2331_;
}
pub unsafe fn l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable(
    mut v_00_u03b1_2332_: *mut leanh::LeanObject,
    mut v_inst_2333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2334_ = leanh::lean_alloc_closure(
        l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2334_, 0, v_inst_2333_);
    return v___f_2334_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation(
    mut v_00_u03b1_2335_: *mut leanh::LeanObject,
    mut v_inst_2336_: *mut leanh::LeanObject,
    mut v_inst_2337_: *mut leanh::LeanObject,
    mut v_inst_2338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2339_ = leanh::lean_box(0);
    return v___x_2339_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___boxed(
    mut v_00_u03b1_2340_: *mut leanh::LeanObject,
    mut v_inst_2341_: *mut leanh::LeanObject,
    mut v_inst_2342_: *mut leanh::LeanObject,
    mut v_inst_2343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2344_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation(v_00_u03b1_2340_, v_inst_2341_, v_inst_2342_, v_inst_2343_);
    leanh::lean_dec_ref(v_inst_2341_);
    return v_res_2344_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation(
    mut v_00_u03b1_2345_: *mut leanh::LeanObject,
    mut v_inst_2346_: *mut leanh::LeanObject,
    mut v_inst_2347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2348_ = leanh::lean_box(0);
    return v___x_2348_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___boxed(
    mut v_00_u03b1_2349_: *mut leanh::LeanObject,
    mut v_inst_2350_: *mut leanh::LeanObject,
    mut v_inst_2351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2352_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation(v_00_u03b1_2349_, v_inst_2350_, v_inst_2351_);
    leanh::lean_dec_ref(v_inst_2350_);
    return v_res_2352_;
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0(
    mut v_inst_2353_: *mut leanh::LeanObject,
    mut v_it_2354_: *mut leanh::LeanObject,
    mut v_n_2355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succMany_x3f_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2361_: u8 = 0;
    let mut v_val_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_it_2354_) == 0 {
                    leanh::lean_dec(v_n_2355_);
                    leanh::lean_dec_ref(v_inst_2353_);
                    v___x_2356_ = leanh::lean_box(2);
                    return v___x_2356_;
                } else {
                    v_succ_x3f_2357_ = leanh::lean_ctor_get(v_inst_2353_, 0);
                    v_succMany_x3f_2358_ = leanh::lean_ctor_get(v_inst_2353_, 1);
                    v_isSharedCheck_2370_ = (!leanh::lean_is_exclusive(v_inst_2353_)) as u8;
                    if v_isSharedCheck_2370_ == 0 {
                        v___x_2360_ = v_inst_2353_;
                        v_isShared_2361_ = v_isSharedCheck_2370_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_succMany_x3f_2358_);
                        leanh::lean_inc(v_succ_x3f_2357_);
                        leanh::lean_dec(v_inst_2353_);
                        v___x_2360_ = leanh::lean_box(0);
                        v_isShared_2361_ = v_isSharedCheck_2370_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_2362_ = leanh::lean_ctor_get(v_it_2354_, 0);
                leanh::lean_inc(v_val_2362_);
                leanh::lean_dec_ref_known(v_it_2354_, 1);
                v___x_2363_ =
                    leanh::lean_apply_2(v_succMany_x3f_2358_, v_n_2355_, v_val_2362_);
                if leanh::lean_obj_tag(v___x_2363_) == 0 {
                    leanh::lean_del_object(v___x_2360_);
                    leanh::lean_dec_ref(v_succ_x3f_2357_);
                    v___x_2364_ = leanh::lean_box(2);
                    return v___x_2364_;
                } else {
                    v_val_2365_ = leanh::lean_ctor_get(v___x_2363_, 0);
                    leanh::lean_inc_n(v_val_2365_, 2);
                    leanh::lean_dec_ref_known(v___x_2363_, 1);
                    v___x_2366_ = leanh::lean_apply_1(v_succ_x3f_2357_, v_val_2365_);
                    if v_isShared_2361_ == 0 {
                        leanh::lean_ctor_set(v___x_2360_, 1, v_val_2365_);
                        leanh::lean_ctor_set(v___x_2360_, 0, v___x_2366_);
                        v___x_2368_ = v___x_2360_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2369_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2369_, 1, v_val_2365_);
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
    mut v_inst_2371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2372_ = leanh::lean_alloc_closure(
        l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2372_, 0, v_inst_2371_);
    return v___f_2372_;
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorAccess(
    mut v_00_u03b1_2373_: *mut leanh::LeanObject,
    mut v_inst_2374_: *mut leanh::LeanObject,
    mut v_inst_2375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2376_ = leanh::lean_alloc_closure(
        l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2376_, 0, v_inst_2374_);
    return v___f_2376_;
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1(
    mut v_toPure_2377_: *mut leanh::LeanObject,
    mut v_inst_2378_: *mut leanh::LeanObject,
    mut v_f_2379_: *mut leanh::LeanObject,
    mut v_toBind_2380_: *mut leanh::LeanObject,
    mut v_next_2381_: *mut leanh::LeanObject,
    mut v_acc_2382_: *mut leanh::LeanObject,
    mut v_h_2383_: *mut leanh::LeanObject,
    mut v_G_2384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_next_2381_);
    v___f_2385_ = leanh::lean_alloc_closure(
        l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2385_, 0, v_toPure_2377_);
    leanh::lean_closure_set(v___f_2385_, 1, v_inst_2378_);
    leanh::lean_closure_set(v___f_2385_, 2, v_next_2381_);
    leanh::lean_closure_set(v___f_2385_, 3, v_G_2384_);
    v___x_2386_ = leanh::lean_apply_3(
        v_f_2379_,
        v_next_2381_,
        leanh::lean_box(0),
        v_acc_2382_,
    );
    v___x_2387_ = leanh::lean_apply_4(
        v_toBind_2380_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2386_,
        v___f_2385_,
    );
    return v___x_2387_;
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg(
    mut v_inst_2388_: *mut leanh::LeanObject,
    mut v_inst_2389_: *mut leanh::LeanObject,
    mut v_acc_2390_: *mut leanh::LeanObject,
    mut v_next_2391_: *mut leanh::LeanObject,
    mut v_f_2392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2393_ = leanh::lean_ctor_get(v_inst_2389_, 0);
    leanh::lean_inc_ref(v_toApplicative_2393_);
    v_toBind_2394_ = leanh::lean_ctor_get(v_inst_2389_, 1);
    leanh::lean_inc(v_toBind_2394_);
    leanh::lean_dec_ref(v_inst_2389_);
    v_toPure_2395_ = leanh::lean_ctor_get(v_toApplicative_2393_, 1);
    leanh::lean_inc(v_toPure_2395_);
    leanh::lean_dec_ref(v_toApplicative_2393_);
    v___f_2396_ = leanh::lean_alloc_closure(
        l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        4,
    );
    leanh::lean_closure_set(v___f_2396_, 0, v_toPure_2395_);
    leanh::lean_closure_set(v___f_2396_, 1, v_inst_2388_);
    leanh::lean_closure_set(v___f_2396_, 2, v_f_2392_);
    leanh::lean_closure_set(v___f_2396_, 3, v_toBind_2394_);
    v___x_2397_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_2396_,
        v_next_2391_,
        v_acc_2390_,
        leanh::lean_box(0),
    );
    return v___x_2397_;
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorLoop_loop(
    mut v_00_u03b1_2398_: *mut leanh::LeanObject,
    mut v_inst_2399_: *mut leanh::LeanObject,
    mut v_inst_2400_: *mut leanh::LeanObject,
    mut v_n_2401_: *mut leanh::LeanObject,
    mut v_inst_2402_: *mut leanh::LeanObject,
    mut v_00_u03b3_2403_: *mut leanh::LeanObject,
    mut v_Pl_2404_: *mut leanh::LeanObject,
    mut v_LargeEnough_2405_: *mut leanh::LeanObject,
    mut v_hl_2406_: *mut leanh::LeanObject,
    mut v_acc_2407_: *mut leanh::LeanObject,
    mut v_next_2408_: *mut leanh::LeanObject,
    mut v_h_2409_: *mut leanh::LeanObject,
    mut v_f_2410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2411_ = leanh::lean_ctor_get(v_inst_2402_, 0);
    leanh::lean_inc_ref(v_toApplicative_2411_);
    v_toBind_2412_ = leanh::lean_ctor_get(v_inst_2402_, 1);
    leanh::lean_inc(v_toBind_2412_);
    leanh::lean_dec_ref(v_inst_2402_);
    v_toPure_2413_ = leanh::lean_ctor_get(v_toApplicative_2411_, 1);
    leanh::lean_inc(v_toPure_2413_);
    leanh::lean_dec_ref(v_toApplicative_2411_);
    v___f_2414_ = leanh::lean_alloc_closure(
        l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        4,
    );
    leanh::lean_closure_set(v___f_2414_, 0, v_toPure_2413_);
    leanh::lean_closure_set(v___f_2414_, 1, v_inst_2399_);
    leanh::lean_closure_set(v___f_2414_, 2, v_f_2410_);
    leanh::lean_closure_set(v___f_2414_, 3, v_toBind_2412_);
    v___x_2415_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_2414_,
        v_next_2408_,
        v_acc_2407_,
        leanh::lean_box(0),
    );
    return v___x_2415_;
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2(
    mut v_toPure_2416_: *mut leanh::LeanObject,
    mut v_inst_2417_: *mut leanh::LeanObject,
    mut v_toBind_2418_: *mut leanh::LeanObject,
    mut v_x_2419_: *mut leanh::LeanObject,
    mut v_00_u03b3_2420_: *mut leanh::LeanObject,
    mut v_Pl_2421_: *mut leanh::LeanObject,
    mut v_it_2422_: *mut leanh::LeanObject,
    mut v_init_2423_: *mut leanh::LeanObject,
    mut v_f_2424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_2422_) == 0 {
        let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_2424_);
        leanh::lean_dec(v_toBind_2418_);
        leanh::lean_dec_ref(v_inst_2417_);
        v___x_2425_ =
            leanh::lean_apply_2(v_toPure_2416_, leanh::lean_box(0), v_init_2423_);
        return v___x_2425_;
    } else {
        let mut v_val_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2426_ = leanh::lean_ctor_get(v_it_2422_, 0);
        leanh::lean_inc(v_val_2426_);
        leanh::lean_dec_ref_known(v_it_2422_, 1);
        v___f_2427_ = leanh::lean_alloc_closure(
            l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1 as *mut core::ffi::c_void,
            8,
            4,
        );
        leanh::lean_closure_set(v___f_2427_, 0, v_toPure_2416_);
        leanh::lean_closure_set(v___f_2427_, 1, v_inst_2417_);
        leanh::lean_closure_set(v___f_2427_, 2, v_f_2424_);
        leanh::lean_closure_set(v___f_2427_, 3, v_toBind_2418_);
        v___x_2428_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_2427_,
            v_val_2426_,
            v_init_2423_,
            leanh::lean_box(0),
        );
        return v___x_2428_;
    }
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed(
    mut v_toPure_2429_: *mut leanh::LeanObject,
    mut v_inst_2430_: *mut leanh::LeanObject,
    mut v_toBind_2431_: *mut leanh::LeanObject,
    mut v_x_2432_: *mut leanh::LeanObject,
    mut v_00_u03b3_2433_: *mut leanh::LeanObject,
    mut v_Pl_2434_: *mut leanh::LeanObject,
    mut v_it_2435_: *mut leanh::LeanObject,
    mut v_init_2436_: *mut leanh::LeanObject,
    mut v_f_2437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_x_2432_);
    return v_res_2438_;
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorLoop___redArg(
    mut v_inst_2439_: *mut leanh::LeanObject,
    mut v_inst_2440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2441_ = leanh::lean_ctor_get(v_inst_2440_, 0);
    leanh::lean_inc_ref(v_toApplicative_2441_);
    v_toBind_2442_ = leanh::lean_ctor_get(v_inst_2440_, 1);
    leanh::lean_inc(v_toBind_2442_);
    leanh::lean_dec_ref(v_inst_2440_);
    v_toPure_2443_ = leanh::lean_ctor_get(v_toApplicative_2441_, 1);
    leanh::lean_inc(v_toPure_2443_);
    leanh::lean_dec_ref(v_toApplicative_2441_);
    v___f_2444_ = leanh::lean_alloc_closure(
        l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed as *mut core::ffi::c_void,
        9,
        3,
    );
    leanh::lean_closure_set(v___f_2444_, 0, v_toPure_2443_);
    leanh::lean_closure_set(v___f_2444_, 1, v_inst_2439_);
    leanh::lean_closure_set(v___f_2444_, 2, v_toBind_2442_);
    return v___f_2444_;
}
pub unsafe fn l_Std_Rxi_Iterator_instIteratorLoop(
    mut v_00_u03b1_2445_: *mut leanh::LeanObject,
    mut v_inst_2446_: *mut leanh::LeanObject,
    mut v_inst_2447_: *mut leanh::LeanObject,
    mut v_n_2448_: *mut leanh::LeanObject,
    mut v_inst_2449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2450_ = leanh::lean_ctor_get(v_inst_2449_, 0);
    leanh::lean_inc_ref(v_toApplicative_2450_);
    v_toBind_2451_ = leanh::lean_ctor_get(v_inst_2449_, 1);
    leanh::lean_inc(v_toBind_2451_);
    leanh::lean_dec_ref(v_inst_2449_);
    v_toPure_2452_ = leanh::lean_ctor_get(v_toApplicative_2450_, 1);
    leanh::lean_inc(v_toPure_2452_);
    leanh::lean_dec_ref(v_toApplicative_2450_);
    v___f_2453_ = leanh::lean_alloc_closure(
        l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed as *mut core::ffi::c_void,
        9,
        3,
    );
    leanh::lean_closure_set(v___f_2453_, 0, v_toPure_2452_);
    leanh::lean_closure_set(v___f_2453_, 1, v_inst_2446_);
    leanh::lean_closure_set(v___f_2453_, 2, v_toBind_2451_);
    return v___f_2453_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___redArg(
    mut v_it_2454_: *mut leanh::LeanObject,
    mut v_f_2455_: *mut leanh::LeanObject,
    mut v_h__1_2456_: *mut leanh::LeanObject,
    mut v_h__2_2457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_2454_) == 0 {
        let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2456_);
        v___x_2458_ = leanh::lean_apply_1(v_h__2_2457_, v_f_2455_);
        return v___x_2458_;
    } else {
        let mut v_val_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2457_);
        v_val_2459_ = leanh::lean_ctor_get(v_it_2454_, 0);
        leanh::lean_inc(v_val_2459_);
        leanh::lean_dec_ref_known(v_it_2454_, 1);
        v___x_2460_ = leanh::lean_apply_2(v_h__1_2456_, v_val_2459_, v_f_2455_);
        return v___x_2460_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter(
    mut v_00_u03b1_2461_: *mut leanh::LeanObject,
    mut v_inst_2462_: *mut leanh::LeanObject,
    mut v_n_2463_: *mut leanh::LeanObject,
    mut v_00_u03b3_2464_: *mut leanh::LeanObject,
    mut v_Pl_2465_: *mut leanh::LeanObject,
    mut v_motive_2466_: *mut leanh::LeanObject,
    mut v_it_2467_: *mut leanh::LeanObject,
    mut v_f_2468_: *mut leanh::LeanObject,
    mut v_h__1_2469_: *mut leanh::LeanObject,
    mut v_h__2_2470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_2467_) == 0 {
        let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2469_);
        v___x_2471_ = leanh::lean_apply_1(v_h__2_2470_, v_f_2468_);
        return v___x_2471_;
    } else {
        let mut v_val_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2470_);
        v_val_2472_ = leanh::lean_ctor_get(v_it_2467_, 0);
        leanh::lean_inc(v_val_2472_);
        leanh::lean_dec_ref_known(v_it_2467_, 1);
        v___x_2473_ = leanh::lean_apply_2(v_h__1_2469_, v_val_2472_, v_f_2468_);
        return v___x_2473_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___boxed(
    mut v_00_u03b1_2474_: *mut leanh::LeanObject,
    mut v_inst_2475_: *mut leanh::LeanObject,
    mut v_n_2476_: *mut leanh::LeanObject,
    mut v_00_u03b3_2477_: *mut leanh::LeanObject,
    mut v_Pl_2478_: *mut leanh::LeanObject,
    mut v_motive_2479_: *mut leanh::LeanObject,
    mut v_it_2480_: *mut leanh::LeanObject,
    mut v_f_2481_: *mut leanh::LeanObject,
    mut v_h__1_2482_: *mut leanh::LeanObject,
    mut v_h__2_2483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2484_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_2474_, v_inst_2475_, v_n_2476_, v_00_u03b3_2477_, v_Pl_2478_, v_motive_2479_, v_it_2480_, v_f_2481_, v_h__1_2482_, v_h__2_2483_);
    leanh::lean_dec_ref(v_inst_2475_);
    return v_res_2484_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_PRange(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_RangeIterator(
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
pub unsafe fn initialize_Init_Data_Range_Polymorphic_RangeIterator(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_PRange(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
}