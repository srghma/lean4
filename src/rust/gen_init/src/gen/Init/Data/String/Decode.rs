// Lean compiler output
// Module: Init.Data.String.Decode
// Imports: Init.Data.Char.Lemmas Init.Data.ByteArray.Basic Init.Data.ByteArray.Lemmas Init.Data.UInt.Basic Init.Data.BitVec.Bootstrap Init.Data.BitVec.Lemmas Init.Data.Nat.Linear Init.Data.Nat.MinMax Init.Data.Option.Lemmas Init.Data.UInt.Bitwise Init.Data.UInt.Lemmas Init.Omega
use crate::ffi::{
    lean_byte_array_fget, lean_byte_array_size, lean_nat_add, lean_nat_dec_lt, lean_uint8_dec_eq,
    lean_uint8_land, lean_uint8_lor, lean_uint8_to_uint32, lean_uint32_dec_le, lean_uint32_dec_lt,
    lean_uint32_lor, lean_uint32_shift_left, lean_uint32_shift_right, lean_uint32_to_uint8,
};
use crate::r#gen::Init::Data::BitVec::Bootstrap::{
    initialize_Init_Data_BitVec_Bootstrap, runtime_initialize_Init_Data_BitVec_Bootstrap,
};
use crate::r#gen::Init::Data::BitVec::Lemmas::{
    initialize_Init_Data_BitVec_Lemmas, runtime_initialize_Init_Data_BitVec_Lemmas,
};
use crate::r#gen::Init::Data::ByteArray::Basic::{
    initialize_Init_Data_ByteArray_Basic, runtime_initialize_Init_Data_ByteArray_Basic,
};
use crate::r#gen::Init::Data::ByteArray::Lemmas::{
    initialize_Init_Data_ByteArray_Lemmas, runtime_initialize_Init_Data_ByteArray_Lemmas,
};
use crate::r#gen::Init::Data::Char::Lemmas::{
    initialize_Init_Data_Char_Lemmas, runtime_initialize_Init_Data_Char_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Nat::MinMax::{
    initialize_Init_Data_Nat_MinMax, runtime_initialize_Init_Data_Nat_MinMax,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::UInt::Basic::{
    initialize_Init_Data_UInt_Basic, runtime_initialize_Init_Data_UInt_Basic,
};
use crate::r#gen::Init::Data::UInt::Bitwise::{
    initialize_Init_Data_UInt_Bitwise, runtime_initialize_Init_Data_UInt_Bitwise,
};
use crate::r#gen::Init::Data::UInt::Lemmas::{
    initialize_Init_Data_UInt_Lemmas, runtime_initialize_Init_Data_UInt_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
pub unsafe fn l_String_utf8EncodeCharFast(mut v_c_1180_: u32) -> *mut crate::leanh::LeanObject {
    let mut v___x_1181_: u32 = 0;
    let mut v___x_1182_: u8 = 0;
    v___x_1181_ = 127;
    v___x_1182_ = lean_uint32_dec_le(v_c_1180_, v___x_1181_);
    if v___x_1182_ == 0 {
        let mut v___x_1183_: u32 = 0;
        let mut v___x_1184_: u8 = 0;
        v___x_1183_ = 2047;
        v___x_1184_ = lean_uint32_dec_le(v_c_1180_, v___x_1183_);
        if v___x_1184_ == 0 {
            let mut v___x_1185_: u32 = 0;
            let mut v___x_1186_: u8 = 0;
            v___x_1185_ = 65535;
            v___x_1186_ = lean_uint32_dec_le(v_c_1180_, v___x_1185_);
            if v___x_1186_ == 0 {
                let mut v___x_1187_: u32 = 0;
                let mut v___x_1188_: u32 = 0;
                let mut v___x_1189_: u8 = 0;
                let mut v___x_1190_: u8 = 0;
                let mut v___x_1191_: u8 = 0;
                let mut v___x_1192_: u8 = 0;
                let mut v___x_1193_: u8 = 0;
                let mut v___x_1194_: u32 = 0;
                let mut v___x_1195_: u32 = 0;
                let mut v___x_1196_: u8 = 0;
                let mut v___x_1197_: u8 = 0;
                let mut v___x_1198_: u8 = 0;
                let mut v___x_1199_: u8 = 0;
                let mut v___x_1200_: u8 = 0;
                let mut v___x_1201_: u32 = 0;
                let mut v___x_1202_: u32 = 0;
                let mut v___x_1203_: u8 = 0;
                let mut v___x_1204_: u8 = 0;
                let mut v___x_1205_: u8 = 0;
                let mut v___x_1206_: u8 = 0;
                let mut v___x_1207_: u8 = 0;
                let mut v___x_1208_: u8 = 0;
                let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1187_ = 18;
                v___x_1188_ = lean_uint32_shift_right(v_c_1180_, v___x_1187_);
                v___x_1189_ = lean_uint32_to_uint8(v___x_1188_);
                v___x_1190_ = 7;
                v___x_1191_ = lean_uint8_land(v___x_1189_, v___x_1190_);
                v___x_1192_ = 240;
                v___x_1193_ = lean_uint8_lor(v___x_1191_, v___x_1192_);
                v___x_1194_ = 12;
                v___x_1195_ = lean_uint32_shift_right(v_c_1180_, v___x_1194_);
                v___x_1196_ = lean_uint32_to_uint8(v___x_1195_);
                v___x_1197_ = 63;
                v___x_1198_ = lean_uint8_land(v___x_1196_, v___x_1197_);
                v___x_1199_ = 128;
                v___x_1200_ = lean_uint8_lor(v___x_1198_, v___x_1199_);
                v___x_1201_ = 6;
                v___x_1202_ = lean_uint32_shift_right(v_c_1180_, v___x_1201_);
                v___x_1203_ = lean_uint32_to_uint8(v___x_1202_);
                v___x_1204_ = lean_uint8_land(v___x_1203_, v___x_1197_);
                v___x_1205_ = lean_uint8_lor(v___x_1204_, v___x_1199_);
                v___x_1206_ = lean_uint32_to_uint8(v_c_1180_);
                v___x_1207_ = lean_uint8_land(v___x_1206_, v___x_1197_);
                v___x_1208_ = lean_uint8_lor(v___x_1207_, v___x_1199_);
                v___x_1209_ = crate::leanh::lean_box(0);
                v___x_1210_ = crate::leanh::lean_box((v___x_1208_) as usize);
                v___x_1211_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1211_, 0, v___x_1210_);
                crate::leanh::lean_ctor_set(v___x_1211_, 1, v___x_1209_);
                v___x_1212_ = crate::leanh::lean_box((v___x_1205_) as usize);
                v___x_1213_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1213_, 0, v___x_1212_);
                crate::leanh::lean_ctor_set(v___x_1213_, 1, v___x_1211_);
                v___x_1214_ = crate::leanh::lean_box((v___x_1200_) as usize);
                v___x_1215_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1215_, 0, v___x_1214_);
                crate::leanh::lean_ctor_set(v___x_1215_, 1, v___x_1213_);
                v___x_1216_ = crate::leanh::lean_box((v___x_1193_) as usize);
                v___x_1217_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1217_, 0, v___x_1216_);
                crate::leanh::lean_ctor_set(v___x_1217_, 1, v___x_1215_);
                return v___x_1217_;
            } else {
                let mut v___x_1218_: u32 = 0;
                let mut v___x_1219_: u32 = 0;
                let mut v___x_1220_: u8 = 0;
                let mut v___x_1221_: u8 = 0;
                let mut v___x_1222_: u8 = 0;
                let mut v___x_1223_: u8 = 0;
                let mut v___x_1224_: u8 = 0;
                let mut v___x_1225_: u32 = 0;
                let mut v___x_1226_: u32 = 0;
                let mut v___x_1227_: u8 = 0;
                let mut v___x_1228_: u8 = 0;
                let mut v___x_1229_: u8 = 0;
                let mut v___x_1230_: u8 = 0;
                let mut v___x_1231_: u8 = 0;
                let mut v___x_1232_: u8 = 0;
                let mut v___x_1233_: u8 = 0;
                let mut v___x_1234_: u8 = 0;
                let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1218_ = 12;
                v___x_1219_ = lean_uint32_shift_right(v_c_1180_, v___x_1218_);
                v___x_1220_ = lean_uint32_to_uint8(v___x_1219_);
                v___x_1221_ = 15;
                v___x_1222_ = lean_uint8_land(v___x_1220_, v___x_1221_);
                v___x_1223_ = 224;
                v___x_1224_ = lean_uint8_lor(v___x_1222_, v___x_1223_);
                v___x_1225_ = 6;
                v___x_1226_ = lean_uint32_shift_right(v_c_1180_, v___x_1225_);
                v___x_1227_ = lean_uint32_to_uint8(v___x_1226_);
                v___x_1228_ = 63;
                v___x_1229_ = lean_uint8_land(v___x_1227_, v___x_1228_);
                v___x_1230_ = 128;
                v___x_1231_ = lean_uint8_lor(v___x_1229_, v___x_1230_);
                v___x_1232_ = lean_uint32_to_uint8(v_c_1180_);
                v___x_1233_ = lean_uint8_land(v___x_1232_, v___x_1228_);
                v___x_1234_ = lean_uint8_lor(v___x_1233_, v___x_1230_);
                v___x_1235_ = crate::leanh::lean_box(0);
                v___x_1236_ = crate::leanh::lean_box((v___x_1234_) as usize);
                v___x_1237_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1237_, 0, v___x_1236_);
                crate::leanh::lean_ctor_set(v___x_1237_, 1, v___x_1235_);
                v___x_1238_ = crate::leanh::lean_box((v___x_1231_) as usize);
                v___x_1239_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1239_, 0, v___x_1238_);
                crate::leanh::lean_ctor_set(v___x_1239_, 1, v___x_1237_);
                v___x_1240_ = crate::leanh::lean_box((v___x_1224_) as usize);
                v___x_1241_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1241_, 0, v___x_1240_);
                crate::leanh::lean_ctor_set(v___x_1241_, 1, v___x_1239_);
                return v___x_1241_;
            }
        } else {
            let mut v___x_1242_: u32 = 0;
            let mut v___x_1243_: u32 = 0;
            let mut v___x_1244_: u8 = 0;
            let mut v___x_1245_: u8 = 0;
            let mut v___x_1246_: u8 = 0;
            let mut v___x_1247_: u8 = 0;
            let mut v___x_1248_: u8 = 0;
            let mut v___x_1249_: u8 = 0;
            let mut v___x_1250_: u8 = 0;
            let mut v___x_1251_: u8 = 0;
            let mut v___x_1252_: u8 = 0;
            let mut v___x_1253_: u8 = 0;
            let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1242_ = 6;
            v___x_1243_ = lean_uint32_shift_right(v_c_1180_, v___x_1242_);
            v___x_1244_ = lean_uint32_to_uint8(v___x_1243_);
            v___x_1245_ = 31;
            v___x_1246_ = lean_uint8_land(v___x_1244_, v___x_1245_);
            v___x_1247_ = 192;
            v___x_1248_ = lean_uint8_lor(v___x_1246_, v___x_1247_);
            v___x_1249_ = lean_uint32_to_uint8(v_c_1180_);
            v___x_1250_ = 63;
            v___x_1251_ = lean_uint8_land(v___x_1249_, v___x_1250_);
            v___x_1252_ = 128;
            v___x_1253_ = lean_uint8_lor(v___x_1251_, v___x_1252_);
            v___x_1254_ = crate::leanh::lean_box(0);
            v___x_1255_ = crate::leanh::lean_box((v___x_1253_) as usize);
            v___x_1256_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1256_, 0, v___x_1255_);
            crate::leanh::lean_ctor_set(v___x_1256_, 1, v___x_1254_);
            v___x_1257_ = crate::leanh::lean_box((v___x_1248_) as usize);
            v___x_1258_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1258_, 0, v___x_1257_);
            crate::leanh::lean_ctor_set(v___x_1258_, 1, v___x_1256_);
            return v___x_1258_;
        }
    } else {
        let mut v___x_1259_: u8 = 0;
        let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1259_ = lean_uint32_to_uint8(v_c_1180_);
        v___x_1260_ = crate::leanh::lean_box(0);
        v___x_1261_ = crate::leanh::lean_box((v___x_1259_) as usize);
        v___x_1262_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1262_, 0, v___x_1261_);
        crate::leanh::lean_ctor_set(v___x_1262_, 1, v___x_1260_);
        return v___x_1262_;
    }
}
pub unsafe fn l_String_utf8EncodeCharFast___boxed(
    mut v_c_1263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1264_: u32 = 0;
    let mut v_res_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1264_ = crate::leanh::lean_unbox_uint32(v_c_1263_);
    crate::leanh::lean_dec(v_c_1263_);
    v_res_1265_ = l_String_utf8EncodeCharFast(v_c_boxed_1264_);
    return v_res_1265_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx(
    mut v_x_1266_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_1266_ {
        0 => {
            let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1267_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1267_;
        }
        1 => {
            let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1268_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1268_;
        }
        2 => {
            let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1269_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1269_;
        }
        3 => {
            let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1270_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1270_;
        }
        _ => {
            let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1271_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_1271_;
        }
    }
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx___boxed(
    mut v_x_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1273_: u8 = 0;
    let mut v_res_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1273_ = (crate::leanh::lean_unbox(v_x_1272_) as u8);
    v_res_1274_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx(v_x_boxed_1273_);
    return v_res_1274_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_toCtorIdx(
    mut v_x_1275_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1276_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorIdx(v_x_1275_);
    return v___x_1276_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_toCtorIdx___boxed(
    mut v_x_1277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1278_: u8 = 0;
    let mut v_res_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1278_ = (crate::leanh::lean_unbox(v_x_1277_) as u8);
    v_res_1279_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_toCtorIdx(v_x_4__boxed_1278_);
    return v_res_1279_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg(
    mut v_k_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1280_);
    return v_k_1280_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg___boxed(
    mut v_k_1281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1282_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___redArg(v_k_1281_);
    crate::leanh::lean_dec(v_k_1281_);
    return v_res_1282_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim(
    mut v_motive_1283_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1284_: *mut crate::leanh::LeanObject,
    mut v_t_1285_: u8,
    mut v_h_1286_: *mut crate::leanh::LeanObject,
    mut v_k_1287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1287_);
    return v_k_1287_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim___boxed(
    mut v_motive_1288_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1289_: *mut crate::leanh::LeanObject,
    mut v_t_1290_: *mut crate::leanh::LeanObject,
    mut v_h_1291_: *mut crate::leanh::LeanObject,
    mut v_k_1292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1293_: u8 = 0;
    let mut v_res_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1293_ = (crate::leanh::lean_unbox(v_t_1290_) as u8);
    v_res_1294_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_ctorElim(
        v_motive_1288_,
        v_ctorIdx_1289_,
        v_t_boxed_1293_,
        v_h_1291_,
        v_k_1292_,
    );
    crate::leanh::lean_dec(v_k_1292_);
    crate::leanh::lean_dec(v_ctorIdx_1289_);
    return v_res_1294_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg(
    mut v_invalid_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_invalid_1295_);
    return v_invalid_1295_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg___boxed(
    mut v_invalid_1296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1297_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___redArg(v_invalid_1296_);
    crate::leanh::lean_dec(v_invalid_1296_);
    return v_res_1297_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim(
    mut v_motive_1298_: *mut crate::leanh::LeanObject,
    mut v_t_1299_: u8,
    mut v_h_1300_: *mut crate::leanh::LeanObject,
    mut v_invalid_1301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_invalid_1301_);
    return v_invalid_1301_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim___boxed(
    mut v_motive_1302_: *mut crate::leanh::LeanObject,
    mut v_t_1303_: *mut crate::leanh::LeanObject,
    mut v_h_1304_: *mut crate::leanh::LeanObject,
    mut v_invalid_1305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1306_: u8 = 0;
    let mut v_res_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1306_ = (crate::leanh::lean_unbox(v_t_1303_) as u8);
    v_res_1307_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_invalid_elim(
        v_motive_1302_,
        v_t_boxed_1306_,
        v_h_1304_,
        v_invalid_1305_,
    );
    crate::leanh::lean_dec(v_invalid_1305_);
    return v_res_1307_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg(
    mut v_done_1308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_done_1308_);
    return v_done_1308_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg___boxed(
    mut v_done_1309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1310_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___redArg(v_done_1309_);
    crate::leanh::lean_dec(v_done_1309_);
    return v_res_1310_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim(
    mut v_motive_1311_: *mut crate::leanh::LeanObject,
    mut v_t_1312_: u8,
    mut v_h_1313_: *mut crate::leanh::LeanObject,
    mut v_done_1314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_done_1314_);
    return v_done_1314_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim___boxed(
    mut v_motive_1315_: *mut crate::leanh::LeanObject,
    mut v_t_1316_: *mut crate::leanh::LeanObject,
    mut v_h_1317_: *mut crate::leanh::LeanObject,
    mut v_done_1318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1319_: u8 = 0;
    let mut v_res_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1319_ = (crate::leanh::lean_unbox(v_t_1316_) as u8);
    v_res_1320_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_done_elim(
        v_motive_1315_,
        v_t_boxed_1319_,
        v_h_1317_,
        v_done_1318_,
    );
    crate::leanh::lean_dec(v_done_1318_);
    return v_res_1320_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg(
    mut v_oneMore_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_oneMore_1321_);
    return v_oneMore_1321_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg___boxed(
    mut v_oneMore_1322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1323_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___redArg(v_oneMore_1322_);
    crate::leanh::lean_dec(v_oneMore_1322_);
    return v_res_1323_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim(
    mut v_motive_1324_: *mut crate::leanh::LeanObject,
    mut v_t_1325_: u8,
    mut v_h_1326_: *mut crate::leanh::LeanObject,
    mut v_oneMore_1327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_oneMore_1327_);
    return v_oneMore_1327_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim___boxed(
    mut v_motive_1328_: *mut crate::leanh::LeanObject,
    mut v_t_1329_: *mut crate::leanh::LeanObject,
    mut v_h_1330_: *mut crate::leanh::LeanObject,
    mut v_oneMore_1331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1332_: u8 = 0;
    let mut v_res_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1332_ = (crate::leanh::lean_unbox(v_t_1329_) as u8);
    v_res_1333_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_oneMore_elim(
        v_motive_1328_,
        v_t_boxed_1332_,
        v_h_1330_,
        v_oneMore_1331_,
    );
    crate::leanh::lean_dec(v_oneMore_1331_);
    return v_res_1333_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg(
    mut v_twoMore_1334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_twoMore_1334_);
    return v_twoMore_1334_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg___boxed(
    mut v_twoMore_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___redArg(v_twoMore_1335_);
    crate::leanh::lean_dec(v_twoMore_1335_);
    return v_res_1336_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim(
    mut v_motive_1337_: *mut crate::leanh::LeanObject,
    mut v_t_1338_: u8,
    mut v_h_1339_: *mut crate::leanh::LeanObject,
    mut v_twoMore_1340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_twoMore_1340_);
    return v_twoMore_1340_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim___boxed(
    mut v_motive_1341_: *mut crate::leanh::LeanObject,
    mut v_t_1342_: *mut crate::leanh::LeanObject,
    mut v_h_1343_: *mut crate::leanh::LeanObject,
    mut v_twoMore_1344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1345_: u8 = 0;
    let mut v_res_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1345_ = (crate::leanh::lean_unbox(v_t_1342_) as u8);
    v_res_1346_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_twoMore_elim(
        v_motive_1341_,
        v_t_boxed_1345_,
        v_h_1343_,
        v_twoMore_1344_,
    );
    crate::leanh::lean_dec(v_twoMore_1344_);
    return v_res_1346_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg(
    mut v_threeMore_1347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_threeMore_1347_);
    return v_threeMore_1347_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg___boxed(
    mut v_threeMore_1348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1349_ =
        l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___redArg(v_threeMore_1348_);
    crate::leanh::lean_dec(v_threeMore_1348_);
    return v_res_1349_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim(
    mut v_motive_1350_: *mut crate::leanh::LeanObject,
    mut v_t_1351_: u8,
    mut v_h_1352_: *mut crate::leanh::LeanObject,
    mut v_threeMore_1353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_threeMore_1353_);
    return v_threeMore_1353_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim___boxed(
    mut v_motive_1354_: *mut crate::leanh::LeanObject,
    mut v_t_1355_: *mut crate::leanh::LeanObject,
    mut v_h_1356_: *mut crate::leanh::LeanObject,
    mut v_threeMore_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1358_: u8 = 0;
    let mut v_res_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1358_ = (crate::leanh::lean_unbox(v_t_1355_) as u8);
    v_res_1359_ = l_ByteArray_utf8DecodeChar_x3f_FirstByte_threeMore_elim(
        v_motive_1354_,
        v_t_boxed_1358_,
        v_h_1356_,
        v_threeMore_1357_,
    );
    crate::leanh::lean_dec(v_threeMore_1357_);
    return v_res_1359_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_parseFirstByte(mut v_b_1360_: u8) -> u8 {
    let mut v___x_1361_: u8 = 0;
    let mut v___x_1362_: u8 = 0;
    let mut v___x_1363_: u8 = 0;
    let mut v___x_1364_: u8 = 0;
    v___x_1361_ = 128;
    v___x_1362_ = lean_uint8_land(v_b_1360_, v___x_1361_);
    v___x_1363_ = 0;
    v___x_1364_ = lean_uint8_dec_eq(v___x_1362_, v___x_1363_);
    if v___x_1364_ == 0 {
        let mut v___x_1365_: u8 = 0;
        let mut v___x_1366_: u8 = 0;
        let mut v___x_1367_: u8 = 0;
        let mut v___x_1368_: u8 = 0;
        v___x_1365_ = 224;
        v___x_1366_ = lean_uint8_land(v_b_1360_, v___x_1365_);
        v___x_1367_ = 192;
        v___x_1368_ = lean_uint8_dec_eq(v___x_1366_, v___x_1367_);
        if v___x_1368_ == 0 {
            let mut v___x_1369_: u8 = 0;
            let mut v___x_1370_: u8 = 0;
            let mut v___x_1371_: u8 = 0;
            v___x_1369_ = 240;
            v___x_1370_ = lean_uint8_land(v_b_1360_, v___x_1369_);
            v___x_1371_ = lean_uint8_dec_eq(v___x_1370_, v___x_1365_);
            if v___x_1371_ == 0 {
                let mut v___x_1372_: u8 = 0;
                let mut v___x_1373_: u8 = 0;
                let mut v___x_1374_: u8 = 0;
                v___x_1372_ = 248;
                v___x_1373_ = lean_uint8_land(v_b_1360_, v___x_1372_);
                v___x_1374_ = lean_uint8_dec_eq(v___x_1373_, v___x_1369_);
                if v___x_1374_ == 0 {
                    let mut v___x_1375_: u8 = 0;
                    v___x_1375_ = 0;
                    return v___x_1375_;
                } else {
                    let mut v___x_1376_: u8 = 0;
                    v___x_1376_ = 4;
                    return v___x_1376_;
                }
            } else {
                let mut v___x_1377_: u8 = 0;
                v___x_1377_ = 3;
                return v___x_1377_;
            }
        } else {
            let mut v___x_1378_: u8 = 0;
            v___x_1378_ = 2;
            return v___x_1378_;
        }
    } else {
        let mut v___x_1379_: u8 = 0;
        v___x_1379_ = 1;
        return v___x_1379_;
    }
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_parseFirstByte___boxed(
    mut v_b_1380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_1381_: u8 = 0;
    let mut v_res_1382_: u8 = 0;
    let mut v_r_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1381_ = (crate::leanh::lean_unbox(v_b_1380_) as u8);
    v_res_1382_ = l_ByteArray_utf8DecodeChar_x3f_parseFirstByte(v_b_boxed_1381_);
    v_r_1383_ = crate::leanh::lean_box((v_res_1382_) as usize);
    return v_r_1383_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte(mut v_b_1384_: u8) -> u8 {
    let mut v___x_1385_: u8 = 0;
    let mut v___x_1386_: u8 = 0;
    let mut v___x_1387_: u8 = 0;
    let mut v___x_1388_: u8 = 0;
    v___x_1385_ = 192;
    v___x_1386_ = lean_uint8_land(v_b_1384_, v___x_1385_);
    v___x_1387_ = 128;
    v___x_1388_ = lean_uint8_dec_eq(v___x_1386_, v___x_1387_);
    if v___x_1388_ == 0 {
        let mut v___x_1389_: u8 = 0;
        v___x_1389_ = 1;
        return v___x_1389_;
    } else {
        let mut v___x_1390_: u8 = 0;
        v___x_1390_ = 0;
        return v___x_1390_;
    }
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte___boxed(
    mut v_b_1391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_1392_: u8 = 0;
    let mut v_res_1393_: u8 = 0;
    let mut v_r_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1392_ = (crate::leanh::lean_unbox(v_b_1391_) as u8);
    v_res_1393_ = l_ByteArray_utf8DecodeChar_x3f_isInvalidContinuationByte(v_b_boxed_1392_);
    v_r_1394_ = crate::leanh::lean_box((v_res_1393_) as usize);
    return v_r_1394_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(
    mut v_w_1395_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1396_: u32 = 0;
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1396_ = lean_uint8_to_uint32(v_w_1395_);
    v___x_1397_ = crate::leanh::lean_box_uint32(v___x_1396_);
    v___x_1398_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1398_, 0, v___x_1397_);
    return v___x_1398_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg___boxed(
    mut v_w_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_boxed_1400_: u8 = 0;
    let mut v_res_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_boxed_1400_ = (crate::leanh::lean_unbox(v_w_1399_) as u8);
    v_res_1401_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___redArg(v_w_boxed_1400_);
    return v_res_1401_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(
    mut v_w_1402_: u8,
    mut v_h_1403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1404_: u32 = 0;
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = lean_uint8_to_uint32(v_w_1402_);
    v___x_1405_ = crate::leanh::lean_box_uint32(v___x_1404_);
    v___x_1406_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1406_, 0, v___x_1405_);
    return v___x_1406_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_assemble_u2081___boxed(
    mut v_w_1407_: *mut crate::leanh::LeanObject,
    mut v_h_1408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_boxed_1409_: u8 = 0;
    let mut v_res_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_boxed_1409_ = (crate::leanh::lean_unbox(v_w_1407_) as u8);
    v_res_1410_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2081(v_w_boxed_1409_, v_h_1408_);
    return v_res_1410_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_verify_u2081(
    mut v_w_1411_: u8,
    mut v___w_1412_: u8,
    mut v___h_1413_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1414_: u8 = 0;
    v___x_1414_ = 1;
    return v___x_1414_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_verify_u2081___boxed(
    mut v_w_1415_: *mut crate::leanh::LeanObject,
    mut v___w_1416_: *mut crate::leanh::LeanObject,
    mut v___h_1417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_boxed_1418_: u8 = 0;
    let mut v___w_boxed_1419_: u8 = 0;
    let mut v_res_1420_: u8 = 0;
    let mut v_r_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_boxed_1418_ = (crate::leanh::lean_unbox(v_w_1415_) as u8);
    v___w_boxed_1419_ = (crate::leanh::lean_unbox(v___w_1416_) as u8);
    v_res_1420_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2081(
        v_w_boxed_1418_,
        v___w_boxed_1419_,
        v___h_1417_,
    );
    v_r_1421_ = crate::leanh::lean_box((v_res_1420_) as usize);
    return v_r_1421_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(
    mut v_w_1422_: u8,
    mut v_x_1423_: u8,
) -> u32 {
    let mut v___x_1424_: u8 = 0;
    let mut v_b_u2080_1425_: u8 = 0;
    let mut v___x_1426_: u8 = 0;
    let mut v_b_u2081_1427_: u8 = 0;
    let mut v___x_1428_: u32 = 0;
    let mut v___x_1429_: u32 = 0;
    let mut v___x_1430_: u32 = 0;
    let mut v___x_1431_: u32 = 0;
    let mut v___x_1432_: u32 = 0;
    v___x_1424_ = 31;
    v_b_u2080_1425_ = lean_uint8_land(v_w_1422_, v___x_1424_);
    v___x_1426_ = 63;
    v_b_u2081_1427_ = lean_uint8_land(v_x_1423_, v___x_1426_);
    v___x_1428_ = lean_uint8_to_uint32(v_b_u2080_1425_);
    v___x_1429_ = 6;
    v___x_1430_ = lean_uint32_shift_left(v___x_1428_, v___x_1429_);
    v___x_1431_ = lean_uint8_to_uint32(v_b_u2081_1427_);
    v___x_1432_ = lean_uint32_lor(v___x_1430_, v___x_1431_);
    return v___x_1432_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked___boxed(
    mut v_w_1433_: *mut crate::leanh::LeanObject,
    mut v_x_1434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_boxed_1435_: u8 = 0;
    let mut v_x_boxed_1436_: u8 = 0;
    let mut v_res_1437_: u32 = 0;
    let mut v_r_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_boxed_1435_ = (crate::leanh::lean_unbox(v_w_1433_) as u8);
    v_x_boxed_1436_ = (crate::leanh::lean_unbox(v_x_1434_) as u8);
    v_res_1437_ =
        l_ByteArray_utf8DecodeChar_x3f_assemble_u2082Unchecked(v_w_boxed_1435_, v_x_boxed_1436_);
    v_r_1438_ = crate::leanh::lean_box_uint32(v_res_1437_);
    return v_r_1438_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_assemble_u2082(
    mut v_w_1439_: u8,
    mut v_x_1440_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1441_: u8 = 0;
    let mut v___x_1442_: u8 = 0;
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: u8 = 0;
    v___x_1441_ = 192;
    v___x_1442_ = lean_uint8_land(v_x_1440_, v___x_1441_);
    v___x_1443_ = 128;
    v___x_1444_ = lean_uint8_dec_eq(v___x_1442_, v___x_1443_);
    if v___x_1444_ == 0 {
        let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1445_ = crate::leanh::lean_box(0);
        return v___x_1445_;
    } else {
        let mut v___x_1446_: u8 = 0;
        let mut v_b_u2080_1447_: u8 = 0;
        let mut v___x_1448_: u8 = 0;
        let mut v_b_u2081_1449_: u8 = 0;
        let mut v___x_1450_: u32 = 0;
        let mut v___x_1451_: u32 = 0;
        let mut v___x_1452_: u32 = 0;
        let mut v___x_1453_: u32 = 0;
        let mut v_r_1454_: u32 = 0;
        let mut v___x_1455_: u32 = 0;
        let mut v___x_1456_: u8 = 0;
        v___x_1446_ = 31;
        v_b_u2080_1447_ = lean_uint8_land(v_w_1439_, v___x_1446_);
        v___x_1448_ = 63;
        v_b_u2081_1449_ = lean_uint8_land(v_x_1440_, v___x_1448_);
        v___x_1450_ = lean_uint8_to_uint32(v_b_u2080_1447_);
        v___x_1451_ = 6;
        v___x_1452_ = lean_uint32_shift_left(v___x_1450_, v___x_1451_);
        v___x_1453_ = lean_uint8_to_uint32(v_b_u2081_1449_);
        v_r_1454_ = lean_uint32_lor(v___x_1452_, v___x_1453_);
        v___x_1455_ = 128;
        v___x_1456_ = lean_uint32_dec_lt(v_r_1454_, v___x_1455_);
        if v___x_1456_ == 0 {
            let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1457_ = crate::leanh::lean_box_uint32(v_r_1454_);
            v___x_1458_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1458_, 0, v___x_1457_);
            return v___x_1458_;
        } else {
            let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1459_ = crate::leanh::lean_box(0);
            return v___x_1459_;
        }
    }
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_assemble_u2082___boxed(
    mut v_w_1460_: *mut crate::leanh::LeanObject,
    mut v_x_1461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_boxed_1462_: u8 = 0;
    let mut v_x_boxed_1463_: u8 = 0;
    let mut v_res_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_boxed_1462_ = (crate::leanh::lean_unbox(v_w_1460_) as u8);
    v_x_boxed_1463_ = (crate::leanh::lean_unbox(v_x_1461_) as u8);
    v_res_1464_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2082(v_w_boxed_1462_, v_x_boxed_1463_);
    return v_res_1464_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_verify_u2082(
    mut v_w_1465_: u8,
    mut v_x_1466_: u8,
) -> u8 {
    let mut v___x_1467_: u8 = 0;
    let mut v___x_1468_: u8 = 0;
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1470_: u8 = 0;
    v___x_1467_ = 192;
    v___x_1468_ = lean_uint8_land(v_x_1466_, v___x_1467_);
    v___x_1469_ = 128;
    v___x_1470_ = lean_uint8_dec_eq(v___x_1468_, v___x_1469_);
    if v___x_1470_ == 0 {
        return v___x_1470_;
    } else {
        let mut v___x_1471_: u8 = 0;
        let mut v_b_u2080_1472_: u8 = 0;
        let mut v___x_1473_: u8 = 0;
        let mut v_b_u2081_1474_: u8 = 0;
        let mut v___x_1475_: u32 = 0;
        let mut v___x_1476_: u32 = 0;
        let mut v___x_1477_: u32 = 0;
        let mut v___x_1478_: u32 = 0;
        let mut v_r_1479_: u32 = 0;
        let mut v___x_1480_: u32 = 0;
        let mut v___x_1481_: u8 = 0;
        v___x_1471_ = 31;
        v_b_u2080_1472_ = lean_uint8_land(v_w_1465_, v___x_1471_);
        v___x_1473_ = 63;
        v_b_u2081_1474_ = lean_uint8_land(v_x_1466_, v___x_1473_);
        v___x_1475_ = lean_uint8_to_uint32(v_b_u2080_1472_);
        v___x_1476_ = 6;
        v___x_1477_ = lean_uint32_shift_left(v___x_1475_, v___x_1476_);
        v___x_1478_ = lean_uint8_to_uint32(v_b_u2081_1474_);
        v_r_1479_ = lean_uint32_lor(v___x_1477_, v___x_1478_);
        v___x_1480_ = 128;
        v___x_1481_ = lean_uint32_dec_le(v___x_1480_, v_r_1479_);
        return v___x_1481_;
    }
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_verify_u2082___boxed(
    mut v_w_1482_: *mut crate::leanh::LeanObject,
    mut v_x_1483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_boxed_1484_: u8 = 0;
    let mut v_x_boxed_1485_: u8 = 0;
    let mut v_res_1486_: u8 = 0;
    let mut v_r_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_boxed_1484_ = (crate::leanh::lean_unbox(v_w_1482_) as u8);
    v_x_boxed_1485_ = (crate::leanh::lean_unbox(v_x_1483_) as u8);
    v_res_1486_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2082(v_w_boxed_1484_, v_x_boxed_1485_);
    v_r_1487_ = crate::leanh::lean_box((v_res_1486_) as usize);
    return v_r_1487_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(
    mut v_w_1488_: u8,
    mut v_x_1489_: u8,
    mut v_y_1490_: u8,
) -> u32 {
    let mut v___x_1491_: u8 = 0;
    let mut v_b_u2080_1492_: u8 = 0;
    let mut v___x_1493_: u8 = 0;
    let mut v_b_u2081_1494_: u8 = 0;
    let mut v_b_u2082_1495_: u8 = 0;
    let mut v___x_1496_: u32 = 0;
    let mut v___x_1497_: u32 = 0;
    let mut v___x_1498_: u32 = 0;
    let mut v___x_1499_: u32 = 0;
    let mut v___x_1500_: u32 = 0;
    let mut v___x_1501_: u32 = 0;
    let mut v___x_1502_: u32 = 0;
    let mut v___x_1503_: u32 = 0;
    let mut v___x_1504_: u32 = 0;
    v___x_1491_ = 15;
    v_b_u2080_1492_ = lean_uint8_land(v_w_1488_, v___x_1491_);
    v___x_1493_ = 63;
    v_b_u2081_1494_ = lean_uint8_land(v_x_1489_, v___x_1493_);
    v_b_u2082_1495_ = lean_uint8_land(v_y_1490_, v___x_1493_);
    v___x_1496_ = lean_uint8_to_uint32(v_b_u2080_1492_);
    v___x_1497_ = 12;
    v___x_1498_ = lean_uint32_shift_left(v___x_1496_, v___x_1497_);
    v___x_1499_ = lean_uint8_to_uint32(v_b_u2081_1494_);
    v___x_1500_ = 6;
    v___x_1501_ = lean_uint32_shift_left(v___x_1499_, v___x_1500_);
    v___x_1502_ = lean_uint32_lor(v___x_1498_, v___x_1501_);
    v___x_1503_ = lean_uint8_to_uint32(v_b_u2082_1495_);
    v___x_1504_ = lean_uint32_lor(v___x_1502_, v___x_1503_);
    return v___x_1504_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked___boxed(
    mut v_w_1505_: *mut crate::leanh::LeanObject,
    mut v_x_1506_: *mut crate::leanh::LeanObject,
    mut v_y_1507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_boxed_1508_: u8 = 0;
    let mut v_x_boxed_1509_: u8 = 0;
    let mut v_y_boxed_1510_: u8 = 0;
    let mut v_res_1511_: u32 = 0;
    let mut v_r_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_boxed_1508_ = (crate::leanh::lean_unbox(v_w_1505_) as u8);
    v_x_boxed_1509_ = (crate::leanh::lean_unbox(v_x_1506_) as u8);
    v_y_boxed_1510_ = (crate::leanh::lean_unbox(v_y_1507_) as u8);
    v_res_1511_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2083Unchecked(
        v_w_boxed_1508_,
        v_x_boxed_1509_,
        v_y_boxed_1510_,
    );
    v_r_1512_ = crate::leanh::lean_box_uint32(v_res_1511_);
    return v_r_1512_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(
    mut v_w_1513_: u8,
    mut v_x_1514_: u8,
    mut v_y_1515_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1516_: u8 = 0;
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: u8 = 0;
    v___x_1516_ = 192;
    v___x_1517_ = lean_uint8_land(v_x_1514_, v___x_1516_);
    v___x_1518_ = 128;
    v___x_1519_ = lean_uint8_dec_eq(v___x_1517_, v___x_1518_);
    if v___x_1519_ == 0 {
        let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1520_ = crate::leanh::lean_box(0);
        return v___x_1520_;
    } else {
        let mut v___x_1521_: u8 = 0;
        let mut v___x_1522_: u8 = 0;
        v___x_1521_ = lean_uint8_land(v_y_1515_, v___x_1516_);
        v___x_1522_ = lean_uint8_dec_eq(v___x_1521_, v___x_1518_);
        if v___x_1522_ == 0 {
            let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1523_ = crate::leanh::lean_box(0);
            return v___x_1523_;
        } else {
            let mut v___x_1524_: u8 = 0;
            let mut v_b_u2080_1525_: u8 = 0;
            let mut v___x_1526_: u8 = 0;
            let mut v_b_u2081_1527_: u8 = 0;
            let mut v_b_u2082_1528_: u8 = 0;
            let mut v___x_1529_: u32 = 0;
            let mut v___x_1530_: u32 = 0;
            let mut v___x_1531_: u32 = 0;
            let mut v___x_1532_: u32 = 0;
            let mut v___x_1533_: u32 = 0;
            let mut v___x_1534_: u32 = 0;
            let mut v___x_1535_: u32 = 0;
            let mut v___x_1536_: u32 = 0;
            let mut v_r_1537_: u32 = 0;
            let mut v___x_1538_: u32 = 0;
            let mut v___x_1539_: u8 = 0;
            v___x_1524_ = 15;
            v_b_u2080_1525_ = lean_uint8_land(v_w_1513_, v___x_1524_);
            v___x_1526_ = 63;
            v_b_u2081_1527_ = lean_uint8_land(v_x_1514_, v___x_1526_);
            v_b_u2082_1528_ = lean_uint8_land(v_y_1515_, v___x_1526_);
            v___x_1529_ = lean_uint8_to_uint32(v_b_u2080_1525_);
            v___x_1530_ = 12;
            v___x_1531_ = lean_uint32_shift_left(v___x_1529_, v___x_1530_);
            v___x_1532_ = lean_uint8_to_uint32(v_b_u2081_1527_);
            v___x_1533_ = 6;
            v___x_1534_ = lean_uint32_shift_left(v___x_1532_, v___x_1533_);
            v___x_1535_ = lean_uint32_lor(v___x_1531_, v___x_1534_);
            v___x_1536_ = lean_uint8_to_uint32(v_b_u2082_1528_);
            v_r_1537_ = lean_uint32_lor(v___x_1535_, v___x_1536_);
            v___x_1538_ = 2048;
            v___x_1539_ = lean_uint32_dec_lt(v_r_1537_, v___x_1538_);
            if v___x_1539_ == 0 {
                let mut v___x_1540_: u32 = 0;
                let mut v___x_1541_: u8 = 0;
                v___x_1540_ = 55296;
                v___x_1541_ = lean_uint32_dec_le(v___x_1540_, v_r_1537_);
                if v___x_1541_ == 0 {
                    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_1542_ = crate::leanh::lean_box_uint32(v_r_1537_);
                    v___x_1543_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1543_, 0, v___x_1542_);
                    return v___x_1543_;
                } else {
                    let mut v___x_1544_: u32 = 0;
                    let mut v___x_1545_: u8 = 0;
                    v___x_1544_ = 57343;
                    v___x_1545_ = lean_uint32_dec_le(v_r_1537_, v___x_1544_);
                    if v___x_1545_ == 0 {
                        let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_1546_ = crate::leanh::lean_box_uint32(v_r_1537_);
                        v___x_1547_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1547_, 0, v___x_1546_);
                        return v___x_1547_;
                    } else {
                        let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_1548_ = crate::leanh::lean_box(0);
                        return v___x_1548_;
                    }
                }
            } else {
                let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1549_ = crate::leanh::lean_box(0);
                return v___x_1549_;
            }
        }
    }
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_assemble_u2083___boxed(
    mut v_w_1550_: *mut crate::leanh::LeanObject,
    mut v_x_1551_: *mut crate::leanh::LeanObject,
    mut v_y_1552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_boxed_1553_: u8 = 0;
    let mut v_x_boxed_1554_: u8 = 0;
    let mut v_y_boxed_1555_: u8 = 0;
    let mut v_res_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_boxed_1553_ = (crate::leanh::lean_unbox(v_w_1550_) as u8);
    v_x_boxed_1554_ = (crate::leanh::lean_unbox(v_x_1551_) as u8);
    v_y_boxed_1555_ = (crate::leanh::lean_unbox(v_y_1552_) as u8);
    v_res_1556_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2083(
        v_w_boxed_1553_,
        v_x_boxed_1554_,
        v_y_boxed_1555_,
    );
    return v_res_1556_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_verify_u2083(
    mut v_w_1557_: u8,
    mut v_x_1558_: u8,
    mut v_y_1559_: u8,
) -> u8 {
    let mut v___x_1560_: u8 = 0;
    let mut v___x_1561_: u8 = 0;
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: u8 = 0;
    v___x_1560_ = 192;
    v___x_1561_ = lean_uint8_land(v_x_1558_, v___x_1560_);
    v___x_1562_ = 128;
    v___x_1563_ = lean_uint8_dec_eq(v___x_1561_, v___x_1562_);
    if v___x_1563_ == 0 {
        return v___x_1563_;
    } else {
        let mut v___x_1564_: u8 = 0;
        let mut v___x_1565_: u8 = 0;
        v___x_1564_ = lean_uint8_land(v_y_1559_, v___x_1560_);
        v___x_1565_ = lean_uint8_dec_eq(v___x_1564_, v___x_1562_);
        if v___x_1565_ == 0 {
            return v___x_1565_;
        } else {
            let mut v___x_1566_: u8 = 0;
            let mut v___x_1567_: u8 = 0;
            let mut v_b_u2080_1568_: u8 = 0;
            let mut v___x_1569_: u8 = 0;
            let mut v_b_u2081_1570_: u8 = 0;
            let mut v_b_u2082_1571_: u8 = 0;
            let mut v___x_1572_: u32 = 0;
            let mut v___x_1573_: u32 = 0;
            let mut v___x_1574_: u32 = 0;
            let mut v___x_1575_: u32 = 0;
            let mut v___x_1576_: u32 = 0;
            let mut v___x_1577_: u32 = 0;
            let mut v___x_1578_: u32 = 0;
            let mut v___x_1579_: u32 = 0;
            let mut v_r_1580_: u32 = 0;
            let mut v___x_1581_: u32 = 0;
            let mut v___x_1582_: u8 = 0;
            v___x_1566_ = 0;
            v___x_1567_ = 15;
            v_b_u2080_1568_ = lean_uint8_land(v_w_1557_, v___x_1567_);
            v___x_1569_ = 63;
            v_b_u2081_1570_ = lean_uint8_land(v_x_1558_, v___x_1569_);
            v_b_u2082_1571_ = lean_uint8_land(v_y_1559_, v___x_1569_);
            v___x_1572_ = lean_uint8_to_uint32(v_b_u2080_1568_);
            v___x_1573_ = 12;
            v___x_1574_ = lean_uint32_shift_left(v___x_1572_, v___x_1573_);
            v___x_1575_ = lean_uint8_to_uint32(v_b_u2081_1570_);
            v___x_1576_ = 6;
            v___x_1577_ = lean_uint32_shift_left(v___x_1575_, v___x_1576_);
            v___x_1578_ = lean_uint32_lor(v___x_1574_, v___x_1577_);
            v___x_1579_ = lean_uint8_to_uint32(v_b_u2082_1571_);
            v_r_1580_ = lean_uint32_lor(v___x_1578_, v___x_1579_);
            v___x_1581_ = 2048;
            v___x_1582_ = lean_uint32_dec_le(v___x_1581_, v_r_1580_);
            if v___x_1582_ == 0 {
                return v___x_1566_;
            } else {
                let mut v___x_1583_: u32 = 0;
                let mut v___x_1584_: u8 = 0;
                v___x_1583_ = 55296;
                v___x_1584_ = lean_uint32_dec_lt(v_r_1580_, v___x_1583_);
                if v___x_1584_ == 0 {
                    let mut v___x_1585_: u32 = 0;
                    let mut v___x_1586_: u8 = 0;
                    v___x_1585_ = 57343;
                    v___x_1586_ = lean_uint32_dec_lt(v___x_1585_, v_r_1580_);
                    if v___x_1586_ == 0 {
                        return v___x_1566_;
                    } else {
                        return v___x_1565_;
                    }
                } else {
                    return v___x_1565_;
                }
            }
        }
    }
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_verify_u2083___boxed(
    mut v_w_1587_: *mut crate::leanh::LeanObject,
    mut v_x_1588_: *mut crate::leanh::LeanObject,
    mut v_y_1589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_boxed_1590_: u8 = 0;
    let mut v_x_boxed_1591_: u8 = 0;
    let mut v_y_boxed_1592_: u8 = 0;
    let mut v_res_1593_: u8 = 0;
    let mut v_r_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_boxed_1590_ = (crate::leanh::lean_unbox(v_w_1587_) as u8);
    v_x_boxed_1591_ = (crate::leanh::lean_unbox(v_x_1588_) as u8);
    v_y_boxed_1592_ = (crate::leanh::lean_unbox(v_y_1589_) as u8);
    v_res_1593_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2083(
        v_w_boxed_1590_,
        v_x_boxed_1591_,
        v_y_boxed_1592_,
    );
    v_r_1594_ = crate::leanh::lean_box((v_res_1593_) as usize);
    return v_r_1594_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(
    mut v_w_1595_: u8,
    mut v_x_1596_: u8,
    mut v_y_1597_: u8,
    mut v_z_1598_: u8,
) -> u32 {
    let mut v___x_1599_: u8 = 0;
    let mut v_b_u2080_1600_: u8 = 0;
    let mut v___x_1601_: u8 = 0;
    let mut v_b_u2081_1602_: u8 = 0;
    let mut v_b_u2082_1603_: u8 = 0;
    let mut v_b_u2083_1604_: u8 = 0;
    let mut v___x_1605_: u32 = 0;
    let mut v___x_1606_: u32 = 0;
    let mut v___x_1607_: u32 = 0;
    let mut v___x_1608_: u32 = 0;
    let mut v___x_1609_: u32 = 0;
    let mut v___x_1610_: u32 = 0;
    let mut v___x_1611_: u32 = 0;
    let mut v___x_1612_: u32 = 0;
    let mut v___x_1613_: u32 = 0;
    let mut v___x_1614_: u32 = 0;
    let mut v___x_1615_: u32 = 0;
    let mut v___x_1616_: u32 = 0;
    let mut v___x_1617_: u32 = 0;
    v___x_1599_ = 7;
    v_b_u2080_1600_ = lean_uint8_land(v_w_1595_, v___x_1599_);
    v___x_1601_ = 63;
    v_b_u2081_1602_ = lean_uint8_land(v_x_1596_, v___x_1601_);
    v_b_u2082_1603_ = lean_uint8_land(v_y_1597_, v___x_1601_);
    v_b_u2083_1604_ = lean_uint8_land(v_z_1598_, v___x_1601_);
    v___x_1605_ = lean_uint8_to_uint32(v_b_u2080_1600_);
    v___x_1606_ = 18;
    v___x_1607_ = lean_uint32_shift_left(v___x_1605_, v___x_1606_);
    v___x_1608_ = lean_uint8_to_uint32(v_b_u2081_1602_);
    v___x_1609_ = 12;
    v___x_1610_ = lean_uint32_shift_left(v___x_1608_, v___x_1609_);
    v___x_1611_ = lean_uint32_lor(v___x_1607_, v___x_1610_);
    v___x_1612_ = lean_uint8_to_uint32(v_b_u2082_1603_);
    v___x_1613_ = 6;
    v___x_1614_ = lean_uint32_shift_left(v___x_1612_, v___x_1613_);
    v___x_1615_ = lean_uint32_lor(v___x_1611_, v___x_1614_);
    v___x_1616_ = lean_uint8_to_uint32(v_b_u2083_1604_);
    v___x_1617_ = lean_uint32_lor(v___x_1615_, v___x_1616_);
    return v___x_1617_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked___boxed(
    mut v_w_1618_: *mut crate::leanh::LeanObject,
    mut v_x_1619_: *mut crate::leanh::LeanObject,
    mut v_y_1620_: *mut crate::leanh::LeanObject,
    mut v_z_1621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_boxed_1622_: u8 = 0;
    let mut v_x_boxed_1623_: u8 = 0;
    let mut v_y_boxed_1624_: u8 = 0;
    let mut v_z_boxed_1625_: u8 = 0;
    let mut v_res_1626_: u32 = 0;
    let mut v_r_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_boxed_1622_ = (crate::leanh::lean_unbox(v_w_1618_) as u8);
    v_x_boxed_1623_ = (crate::leanh::lean_unbox(v_x_1619_) as u8);
    v_y_boxed_1624_ = (crate::leanh::lean_unbox(v_y_1620_) as u8);
    v_z_boxed_1625_ = (crate::leanh::lean_unbox(v_z_1621_) as u8);
    v_res_1626_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084Unchecked(
        v_w_boxed_1622_,
        v_x_boxed_1623_,
        v_y_boxed_1624_,
        v_z_boxed_1625_,
    );
    v_r_1627_ = crate::leanh::lean_box_uint32(v_res_1626_);
    return v_r_1627_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(
    mut v_w_1628_: u8,
    mut v_x_1629_: u8,
    mut v_y_1630_: u8,
    mut v_z_1631_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1633_: u8 = 0;
    let mut v___x_1634_: u8 = 0;
    let mut v___x_1635_: u8 = 0;
    v___x_1632_ = 192;
    v___x_1633_ = lean_uint8_land(v_x_1629_, v___x_1632_);
    v___x_1634_ = 128;
    v___x_1635_ = lean_uint8_dec_eq(v___x_1633_, v___x_1634_);
    if v___x_1635_ == 0 {
        let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1636_ = crate::leanh::lean_box(0);
        return v___x_1636_;
    } else {
        let mut v___x_1637_: u8 = 0;
        let mut v___x_1638_: u8 = 0;
        v___x_1637_ = lean_uint8_land(v_y_1630_, v___x_1632_);
        v___x_1638_ = lean_uint8_dec_eq(v___x_1637_, v___x_1634_);
        if v___x_1638_ == 0 {
            let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1639_ = crate::leanh::lean_box(0);
            return v___x_1639_;
        } else {
            let mut v___x_1640_: u8 = 0;
            let mut v___x_1641_: u8 = 0;
            v___x_1640_ = lean_uint8_land(v_z_1631_, v___x_1632_);
            v___x_1641_ = lean_uint8_dec_eq(v___x_1640_, v___x_1634_);
            if v___x_1641_ == 0 {
                let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1642_ = crate::leanh::lean_box(0);
                return v___x_1642_;
            } else {
                let mut v___x_1643_: u8 = 0;
                let mut v_b_u2080_1644_: u8 = 0;
                let mut v___x_1645_: u8 = 0;
                let mut v_b_u2081_1646_: u8 = 0;
                let mut v_b_u2082_1647_: u8 = 0;
                let mut v_b_u2083_1648_: u8 = 0;
                let mut v___x_1649_: u32 = 0;
                let mut v___x_1650_: u32 = 0;
                let mut v___x_1651_: u32 = 0;
                let mut v___x_1652_: u32 = 0;
                let mut v___x_1653_: u32 = 0;
                let mut v___x_1654_: u32 = 0;
                let mut v___x_1655_: u32 = 0;
                let mut v___x_1656_: u32 = 0;
                let mut v___x_1657_: u32 = 0;
                let mut v___x_1658_: u32 = 0;
                let mut v___x_1659_: u32 = 0;
                let mut v___x_1660_: u32 = 0;
                let mut v_r_1661_: u32 = 0;
                let mut v___x_1662_: u32 = 0;
                let mut v___x_1663_: u8 = 0;
                v___x_1643_ = 7;
                v_b_u2080_1644_ = lean_uint8_land(v_w_1628_, v___x_1643_);
                v___x_1645_ = 63;
                v_b_u2081_1646_ = lean_uint8_land(v_x_1629_, v___x_1645_);
                v_b_u2082_1647_ = lean_uint8_land(v_y_1630_, v___x_1645_);
                v_b_u2083_1648_ = lean_uint8_land(v_z_1631_, v___x_1645_);
                v___x_1649_ = lean_uint8_to_uint32(v_b_u2080_1644_);
                v___x_1650_ = 18;
                v___x_1651_ = lean_uint32_shift_left(v___x_1649_, v___x_1650_);
                v___x_1652_ = lean_uint8_to_uint32(v_b_u2081_1646_);
                v___x_1653_ = 12;
                v___x_1654_ = lean_uint32_shift_left(v___x_1652_, v___x_1653_);
                v___x_1655_ = lean_uint32_lor(v___x_1651_, v___x_1654_);
                v___x_1656_ = lean_uint8_to_uint32(v_b_u2082_1647_);
                v___x_1657_ = 6;
                v___x_1658_ = lean_uint32_shift_left(v___x_1656_, v___x_1657_);
                v___x_1659_ = lean_uint32_lor(v___x_1655_, v___x_1658_);
                v___x_1660_ = lean_uint8_to_uint32(v_b_u2083_1648_);
                v_r_1661_ = lean_uint32_lor(v___x_1659_, v___x_1660_);
                v___x_1662_ = 65536;
                v___x_1663_ = lean_uint32_dec_lt(v_r_1661_, v___x_1662_);
                if v___x_1663_ == 0 {
                    let mut v___x_1664_: u32 = 0;
                    let mut v___x_1665_: u8 = 0;
                    v___x_1664_ = 1114111;
                    v___x_1665_ = lean_uint32_dec_lt(v___x_1664_, v_r_1661_);
                    if v___x_1665_ == 0 {
                        let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_1666_ = crate::leanh::lean_box_uint32(v_r_1661_);
                        v___x_1667_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1667_, 0, v___x_1666_);
                        return v___x_1667_;
                    } else {
                        let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_1668_ = crate::leanh::lean_box(0);
                        return v___x_1668_;
                    }
                } else {
                    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_1669_ = crate::leanh::lean_box(0);
                    return v___x_1669_;
                }
            }
        }
    }
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_assemble_u2084___boxed(
    mut v_w_1670_: *mut crate::leanh::LeanObject,
    mut v_x_1671_: *mut crate::leanh::LeanObject,
    mut v_y_1672_: *mut crate::leanh::LeanObject,
    mut v_z_1673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_boxed_1674_: u8 = 0;
    let mut v_x_boxed_1675_: u8 = 0;
    let mut v_y_boxed_1676_: u8 = 0;
    let mut v_z_boxed_1677_: u8 = 0;
    let mut v_res_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_boxed_1674_ = (crate::leanh::lean_unbox(v_w_1670_) as u8);
    v_x_boxed_1675_ = (crate::leanh::lean_unbox(v_x_1671_) as u8);
    v_y_boxed_1676_ = (crate::leanh::lean_unbox(v_y_1672_) as u8);
    v_z_boxed_1677_ = (crate::leanh::lean_unbox(v_z_1673_) as u8);
    v_res_1678_ = l_ByteArray_utf8DecodeChar_x3f_assemble_u2084(
        v_w_boxed_1674_,
        v_x_boxed_1675_,
        v_y_boxed_1676_,
        v_z_boxed_1677_,
    );
    return v_res_1678_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_verify_u2084(
    mut v_w_1679_: u8,
    mut v_x_1680_: u8,
    mut v_y_1681_: u8,
    mut v_z_1682_: u8,
) -> u8 {
    let mut v___x_1683_: u8 = 0;
    let mut v___x_1684_: u8 = 0;
    let mut v___x_1685_: u8 = 0;
    let mut v___x_1686_: u8 = 0;
    v___x_1683_ = 192;
    v___x_1684_ = lean_uint8_land(v_x_1680_, v___x_1683_);
    v___x_1685_ = 128;
    v___x_1686_ = lean_uint8_dec_eq(v___x_1684_, v___x_1685_);
    if v___x_1686_ == 0 {
        return v___x_1686_;
    } else {
        let mut v___x_1687_: u8 = 0;
        let mut v___x_1688_: u8 = 0;
        v___x_1687_ = lean_uint8_land(v_y_1681_, v___x_1683_);
        v___x_1688_ = lean_uint8_dec_eq(v___x_1687_, v___x_1685_);
        if v___x_1688_ == 0 {
            return v___x_1688_;
        } else {
            let mut v___x_1689_: u8 = 0;
            let mut v___x_1690_: u8 = 0;
            v___x_1689_ = lean_uint8_land(v_z_1682_, v___x_1683_);
            v___x_1690_ = lean_uint8_dec_eq(v___x_1689_, v___x_1685_);
            if v___x_1690_ == 0 {
                return v___x_1690_;
            } else {
                let mut v___x_1691_: u8 = 0;
                let mut v___x_1692_: u8 = 0;
                let mut v_b_u2080_1693_: u8 = 0;
                let mut v___x_1694_: u8 = 0;
                let mut v_b_u2081_1695_: u8 = 0;
                let mut v_b_u2082_1696_: u8 = 0;
                let mut v_b_u2083_1697_: u8 = 0;
                let mut v___x_1698_: u32 = 0;
                let mut v___x_1699_: u32 = 0;
                let mut v___x_1700_: u32 = 0;
                let mut v___x_1701_: u32 = 0;
                let mut v___x_1702_: u32 = 0;
                let mut v___x_1703_: u32 = 0;
                let mut v___x_1704_: u32 = 0;
                let mut v___x_1705_: u32 = 0;
                let mut v___x_1706_: u32 = 0;
                let mut v___x_1707_: u32 = 0;
                let mut v___x_1708_: u32 = 0;
                let mut v___x_1709_: u32 = 0;
                let mut v_r_1710_: u32 = 0;
                let mut v___x_1711_: u32 = 0;
                let mut v___x_1712_: u8 = 0;
                v___x_1691_ = 0;
                v___x_1692_ = 7;
                v_b_u2080_1693_ = lean_uint8_land(v_w_1679_, v___x_1692_);
                v___x_1694_ = 63;
                v_b_u2081_1695_ = lean_uint8_land(v_x_1680_, v___x_1694_);
                v_b_u2082_1696_ = lean_uint8_land(v_y_1681_, v___x_1694_);
                v_b_u2083_1697_ = lean_uint8_land(v_z_1682_, v___x_1694_);
                v___x_1698_ = lean_uint8_to_uint32(v_b_u2080_1693_);
                v___x_1699_ = 18;
                v___x_1700_ = lean_uint32_shift_left(v___x_1698_, v___x_1699_);
                v___x_1701_ = lean_uint8_to_uint32(v_b_u2081_1695_);
                v___x_1702_ = 12;
                v___x_1703_ = lean_uint32_shift_left(v___x_1701_, v___x_1702_);
                v___x_1704_ = lean_uint32_lor(v___x_1700_, v___x_1703_);
                v___x_1705_ = lean_uint8_to_uint32(v_b_u2082_1696_);
                v___x_1706_ = 6;
                v___x_1707_ = lean_uint32_shift_left(v___x_1705_, v___x_1706_);
                v___x_1708_ = lean_uint32_lor(v___x_1704_, v___x_1707_);
                v___x_1709_ = lean_uint8_to_uint32(v_b_u2083_1697_);
                v_r_1710_ = lean_uint32_lor(v___x_1708_, v___x_1709_);
                v___x_1711_ = 65536;
                v___x_1712_ = lean_uint32_dec_le(v___x_1711_, v_r_1710_);
                if v___x_1712_ == 0 {
                    return v___x_1691_;
                } else {
                    let mut v___x_1713_: u32 = 0;
                    let mut v___x_1714_: u8 = 0;
                    v___x_1713_ = 1114111;
                    v___x_1714_ = lean_uint32_dec_le(v_r_1710_, v___x_1713_);
                    if v___x_1714_ == 0 {
                        return v___x_1691_;
                    } else {
                        return v___x_1690_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f_verify_u2084___boxed(
    mut v_w_1715_: *mut crate::leanh::LeanObject,
    mut v_x_1716_: *mut crate::leanh::LeanObject,
    mut v_y_1717_: *mut crate::leanh::LeanObject,
    mut v_z_1718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_boxed_1719_: u8 = 0;
    let mut v_x_boxed_1720_: u8 = 0;
    let mut v_y_boxed_1721_: u8 = 0;
    let mut v_z_boxed_1722_: u8 = 0;
    let mut v_res_1723_: u8 = 0;
    let mut v_r_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_w_boxed_1719_ = (crate::leanh::lean_unbox(v_w_1715_) as u8);
    v_x_boxed_1720_ = (crate::leanh::lean_unbox(v_x_1716_) as u8);
    v_y_boxed_1721_ = (crate::leanh::lean_unbox(v_y_1717_) as u8);
    v_z_boxed_1722_ = (crate::leanh::lean_unbox(v_z_1718_) as u8);
    v_res_1723_ = l_ByteArray_utf8DecodeChar_x3f_verify_u2084(
        v_w_boxed_1719_,
        v_x_boxed_1720_,
        v_y_boxed_1721_,
        v_z_boxed_1722_,
    );
    v_r_1724_ = crate::leanh::lean_box((v_res_1723_) as usize);
    return v_r_1724_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f(
    mut v_bytes_1725_: *mut crate::leanh::LeanObject,
    mut v_i_1726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: u8 = 0;
    v___x_1727_ = lean_byte_array_size(v_bytes_1725_);
    v___x_1728_ = lean_nat_dec_lt(v_i_1726_, v___x_1727_);
    if v___x_1728_ == 0 {
        let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1729_ = crate::leanh::lean_box(0);
        return v___x_1729_;
    } else {
        let mut v___x_1730_: u8 = 0;
        let mut v___x_1731_: u8 = 0;
        let mut v___x_1732_: u8 = 0;
        let mut v___x_1733_: u8 = 0;
        let mut v___x_1734_: u8 = 0;
        v___x_1730_ = lean_byte_array_fget(v_bytes_1725_, v_i_1726_);
        v___x_1731_ = 128;
        v___x_1732_ = lean_uint8_land(v___x_1730_, v___x_1731_);
        v___x_1733_ = 0;
        v___x_1734_ = lean_uint8_dec_eq(v___x_1732_, v___x_1733_);
        if v___x_1734_ == 0 {
            let mut v___x_1735_: u8 = 0;
            let mut v___x_1736_: u8 = 0;
            let mut v___x_1737_: u8 = 0;
            let mut v___x_1738_: u8 = 0;
            v___x_1735_ = 224;
            v___x_1736_ = lean_uint8_land(v___x_1730_, v___x_1735_);
            v___x_1737_ = 192;
            v___x_1738_ = lean_uint8_dec_eq(v___x_1736_, v___x_1737_);
            if v___x_1738_ == 0 {
                let mut v___x_1739_: u8 = 0;
                let mut v___x_1740_: u8 = 0;
                let mut v___x_1741_: u8 = 0;
                v___x_1739_ = 240;
                v___x_1740_ = lean_uint8_land(v___x_1730_, v___x_1739_);
                v___x_1741_ = lean_uint8_dec_eq(v___x_1740_, v___x_1735_);
                if v___x_1741_ == 0 {
                    let mut v___x_1742_: u8 = 0;
                    let mut v___x_1743_: u8 = 0;
                    let mut v___x_1744_: u8 = 0;
                    v___x_1742_ = 248;
                    v___x_1743_ = lean_uint8_land(v___x_1730_, v___x_1742_);
                    v___x_1744_ = lean_uint8_dec_eq(v___x_1743_, v___x_1739_);
                    if v___x_1744_ == 0 {
                        let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_1745_ = crate::leanh::lean_box(0);
                        return v___x_1745_;
                    } else {
                        let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1748_: u8 = 0;
                        v___x_1746_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_1747_ = lean_nat_add(v_i_1726_, v___x_1746_);
                        v___x_1748_ = lean_nat_dec_lt(v___x_1747_, v___x_1727_);
                        if v___x_1748_ == 0 {
                            let mut v___x_1749_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v___x_1747_);
                            v___x_1749_ = crate::leanh::lean_box(0);
                            return v___x_1749_;
                        } else {
                            let mut v___x_1750_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1751_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1752_: u8 = 0;
                            let mut v___x_1753_: u8 = 0;
                            let mut v___x_1754_: u8 = 0;
                            v___x_1750_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1751_ = lean_nat_add(v_i_1726_, v___x_1750_);
                            v___x_1752_ = lean_byte_array_fget(v_bytes_1725_, v___x_1751_);
                            crate::leanh::lean_dec(v___x_1751_);
                            v___x_1753_ = lean_uint8_land(v___x_1752_, v___x_1737_);
                            v___x_1754_ = lean_uint8_dec_eq(v___x_1753_, v___x_1731_);
                            if v___x_1754_ == 0 {
                                let mut v___x_1755_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                crate::leanh::lean_dec(v___x_1747_);
                                v___x_1755_ = crate::leanh::lean_box(0);
                                return v___x_1755_;
                            } else {
                                let mut v___x_1756_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1757_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1758_: u8 = 0;
                                let mut v___x_1759_: u8 = 0;
                                let mut v___x_1760_: u8 = 0;
                                v___x_1756_ = crate::leanh::lean_unsigned_to_nat(2);
                                v___x_1757_ = lean_nat_add(v_i_1726_, v___x_1756_);
                                v___x_1758_ = lean_byte_array_fget(v_bytes_1725_, v___x_1757_);
                                crate::leanh::lean_dec(v___x_1757_);
                                v___x_1759_ = lean_uint8_land(v___x_1758_, v___x_1737_);
                                v___x_1760_ = lean_uint8_dec_eq(v___x_1759_, v___x_1731_);
                                if v___x_1760_ == 0 {
                                    let mut v___x_1761_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    crate::leanh::lean_dec(v___x_1747_);
                                    v___x_1761_ = crate::leanh::lean_box(0);
                                    return v___x_1761_;
                                } else {
                                    let mut v___x_1762_: u8 = 0;
                                    let mut v___x_1763_: u8 = 0;
                                    let mut v___x_1764_: u8 = 0;
                                    v___x_1762_ = lean_byte_array_fget(v_bytes_1725_, v___x_1747_);
                                    crate::leanh::lean_dec(v___x_1747_);
                                    v___x_1763_ = lean_uint8_land(v___x_1762_, v___x_1737_);
                                    v___x_1764_ = lean_uint8_dec_eq(v___x_1763_, v___x_1731_);
                                    if v___x_1764_ == 0 {
                                        let mut v___x_1765_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        v___x_1765_ = crate::leanh::lean_box(0);
                                        return v___x_1765_;
                                    } else {
                                        let mut v___x_1766_: u8 = 0;
                                        let mut v_b_u2080_1767_: u8 = 0;
                                        let mut v___x_1768_: u8 = 0;
                                        let mut v_b_u2081_1769_: u8 = 0;
                                        let mut v_b_u2082_1770_: u8 = 0;
                                        let mut v_b_u2083_1771_: u8 = 0;
                                        let mut v___x_1772_: u32 = 0;
                                        let mut v___x_1773_: u32 = 0;
                                        let mut v___x_1774_: u32 = 0;
                                        let mut v___x_1775_: u32 = 0;
                                        let mut v___x_1776_: u32 = 0;
                                        let mut v___x_1777_: u32 = 0;
                                        let mut v___x_1778_: u32 = 0;
                                        let mut v___x_1779_: u32 = 0;
                                        let mut v___x_1780_: u32 = 0;
                                        let mut v___x_1781_: u32 = 0;
                                        let mut v___x_1782_: u32 = 0;
                                        let mut v___x_1783_: u32 = 0;
                                        let mut v_r_1784_: u32 = 0;
                                        let mut v___x_1785_: u32 = 0;
                                        let mut v___x_1786_: u8 = 0;
                                        v___x_1766_ = 7;
                                        v_b_u2080_1767_ = lean_uint8_land(v___x_1730_, v___x_1766_);
                                        v___x_1768_ = 63;
                                        v_b_u2081_1769_ = lean_uint8_land(v___x_1752_, v___x_1768_);
                                        v_b_u2082_1770_ = lean_uint8_land(v___x_1758_, v___x_1768_);
                                        v_b_u2083_1771_ = lean_uint8_land(v___x_1762_, v___x_1768_);
                                        v___x_1772_ = lean_uint8_to_uint32(v_b_u2080_1767_);
                                        v___x_1773_ = 18;
                                        v___x_1774_ =
                                            lean_uint32_shift_left(v___x_1772_, v___x_1773_);
                                        v___x_1775_ = lean_uint8_to_uint32(v_b_u2081_1769_);
                                        v___x_1776_ = 12;
                                        v___x_1777_ =
                                            lean_uint32_shift_left(v___x_1775_, v___x_1776_);
                                        v___x_1778_ = lean_uint32_lor(v___x_1774_, v___x_1777_);
                                        v___x_1779_ = lean_uint8_to_uint32(v_b_u2082_1770_);
                                        v___x_1780_ = 6;
                                        v___x_1781_ =
                                            lean_uint32_shift_left(v___x_1779_, v___x_1780_);
                                        v___x_1782_ = lean_uint32_lor(v___x_1778_, v___x_1781_);
                                        v___x_1783_ = lean_uint8_to_uint32(v_b_u2083_1771_);
                                        v_r_1784_ = lean_uint32_lor(v___x_1782_, v___x_1783_);
                                        v___x_1785_ = 65536;
                                        v___x_1786_ = lean_uint32_dec_lt(v_r_1784_, v___x_1785_);
                                        if v___x_1786_ == 0 {
                                            let mut v___x_1787_: u32 = 0;
                                            let mut v___x_1788_: u8 = 0;
                                            v___x_1787_ = 1114111;
                                            v___x_1788_ =
                                                lean_uint32_dec_lt(v___x_1787_, v_r_1784_);
                                            if v___x_1788_ == 0 {
                                                let mut v___x_1789_: *mut crate::leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_1790_: *mut crate::leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                v___x_1789_ =
                                                    crate::leanh::lean_box_uint32(v_r_1784_);
                                                v___x_1790_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_1790_,
                                                    0,
                                                    v___x_1789_,
                                                );
                                                return v___x_1790_;
                                            } else {
                                                let mut v___x_1791_: *mut crate::leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                v___x_1791_ = crate::leanh::lean_box(0);
                                                return v___x_1791_;
                                            }
                                        } else {
                                            let mut v___x_1792_: *mut crate::leanh::LeanObject =
                                                core::ptr::null_mut();
                                            v___x_1792_ = crate::leanh::lean_box(0);
                                            return v___x_1792_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1795_: u8 = 0;
                    v___x_1793_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_1794_ = lean_nat_add(v_i_1726_, v___x_1793_);
                    v___x_1795_ = lean_nat_dec_lt(v___x_1794_, v___x_1727_);
                    if v___x_1795_ == 0 {
                        let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v___x_1794_);
                        v___x_1796_ = crate::leanh::lean_box(0);
                        return v___x_1796_;
                    } else {
                        let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1799_: u8 = 0;
                        let mut v___x_1800_: u8 = 0;
                        let mut v___x_1801_: u8 = 0;
                        v___x_1797_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1798_ = lean_nat_add(v_i_1726_, v___x_1797_);
                        v___x_1799_ = lean_byte_array_fget(v_bytes_1725_, v___x_1798_);
                        crate::leanh::lean_dec(v___x_1798_);
                        v___x_1800_ = lean_uint8_land(v___x_1799_, v___x_1737_);
                        v___x_1801_ = lean_uint8_dec_eq(v___x_1800_, v___x_1731_);
                        if v___x_1801_ == 0 {
                            let mut v___x_1802_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v___x_1794_);
                            v___x_1802_ = crate::leanh::lean_box(0);
                            return v___x_1802_;
                        } else {
                            let mut v___x_1803_: u8 = 0;
                            let mut v___x_1804_: u8 = 0;
                            let mut v___x_1805_: u8 = 0;
                            v___x_1803_ = lean_byte_array_fget(v_bytes_1725_, v___x_1794_);
                            crate::leanh::lean_dec(v___x_1794_);
                            v___x_1804_ = lean_uint8_land(v___x_1803_, v___x_1737_);
                            v___x_1805_ = lean_uint8_dec_eq(v___x_1804_, v___x_1731_);
                            if v___x_1805_ == 0 {
                                let mut v___x_1806_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                v___x_1806_ = crate::leanh::lean_box(0);
                                return v___x_1806_;
                            } else {
                                let mut v___x_1807_: u8 = 0;
                                let mut v_b_u2080_1808_: u8 = 0;
                                let mut v___x_1809_: u8 = 0;
                                let mut v_b_u2081_1810_: u8 = 0;
                                let mut v_b_u2082_1811_: u8 = 0;
                                let mut v___x_1812_: u32 = 0;
                                let mut v___x_1813_: u32 = 0;
                                let mut v___x_1814_: u32 = 0;
                                let mut v___x_1815_: u32 = 0;
                                let mut v___x_1816_: u32 = 0;
                                let mut v___x_1817_: u32 = 0;
                                let mut v___x_1818_: u32 = 0;
                                let mut v___x_1819_: u32 = 0;
                                let mut v_r_1820_: u32 = 0;
                                let mut v___x_1821_: u32 = 0;
                                let mut v___x_1822_: u8 = 0;
                                v___x_1807_ = 15;
                                v_b_u2080_1808_ = lean_uint8_land(v___x_1730_, v___x_1807_);
                                v___x_1809_ = 63;
                                v_b_u2081_1810_ = lean_uint8_land(v___x_1799_, v___x_1809_);
                                v_b_u2082_1811_ = lean_uint8_land(v___x_1803_, v___x_1809_);
                                v___x_1812_ = lean_uint8_to_uint32(v_b_u2080_1808_);
                                v___x_1813_ = 12;
                                v___x_1814_ = lean_uint32_shift_left(v___x_1812_, v___x_1813_);
                                v___x_1815_ = lean_uint8_to_uint32(v_b_u2081_1810_);
                                v___x_1816_ = 6;
                                v___x_1817_ = lean_uint32_shift_left(v___x_1815_, v___x_1816_);
                                v___x_1818_ = lean_uint32_lor(v___x_1814_, v___x_1817_);
                                v___x_1819_ = lean_uint8_to_uint32(v_b_u2082_1811_);
                                v_r_1820_ = lean_uint32_lor(v___x_1818_, v___x_1819_);
                                v___x_1821_ = 2048;
                                v___x_1822_ = lean_uint32_dec_lt(v_r_1820_, v___x_1821_);
                                if v___x_1822_ == 0 {
                                    let mut v___x_1823_: u32 = 0;
                                    let mut v___x_1824_: u8 = 0;
                                    v___x_1823_ = 55296;
                                    v___x_1824_ = lean_uint32_dec_le(v___x_1823_, v_r_1820_);
                                    if v___x_1824_ == 0 {
                                        let mut v___x_1825_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1826_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        v___x_1825_ = crate::leanh::lean_box_uint32(v_r_1820_);
                                        v___x_1826_ =
                                            crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1826_, 0, v___x_1825_);
                                        return v___x_1826_;
                                    } else {
                                        let mut v___x_1827_: u32 = 0;
                                        let mut v___x_1828_: u8 = 0;
                                        v___x_1827_ = 57343;
                                        v___x_1828_ = lean_uint32_dec_le(v_r_1820_, v___x_1827_);
                                        if v___x_1828_ == 0 {
                                            let mut v___x_1829_: *mut crate::leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_1830_: *mut crate::leanh::LeanObject =
                                                core::ptr::null_mut();
                                            v___x_1829_ = crate::leanh::lean_box_uint32(v_r_1820_);
                                            v___x_1830_ =
                                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1830_,
                                                0,
                                                v___x_1829_,
                                            );
                                            return v___x_1830_;
                                        } else {
                                            let mut v___x_1831_: *mut crate::leanh::LeanObject =
                                                core::ptr::null_mut();
                                            v___x_1831_ = crate::leanh::lean_box(0);
                                            return v___x_1831_;
                                        }
                                    }
                                } else {
                                    let mut v___x_1832_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    v___x_1832_ = crate::leanh::lean_box(0);
                                    return v___x_1832_;
                                }
                            }
                        }
                    }
                }
            } else {
                let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1835_: u8 = 0;
                v___x_1833_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1834_ = lean_nat_add(v_i_1726_, v___x_1833_);
                v___x_1835_ = lean_nat_dec_lt(v___x_1834_, v___x_1727_);
                if v___x_1835_ == 0 {
                    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_1834_);
                    v___x_1836_ = crate::leanh::lean_box(0);
                    return v___x_1836_;
                } else {
                    let mut v___x_1837_: u8 = 0;
                    let mut v___x_1838_: u8 = 0;
                    let mut v___x_1839_: u8 = 0;
                    v___x_1837_ = lean_byte_array_fget(v_bytes_1725_, v___x_1834_);
                    crate::leanh::lean_dec(v___x_1834_);
                    v___x_1838_ = lean_uint8_land(v___x_1837_, v___x_1737_);
                    v___x_1839_ = lean_uint8_dec_eq(v___x_1838_, v___x_1731_);
                    if v___x_1839_ == 0 {
                        let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_1840_ = crate::leanh::lean_box(0);
                        return v___x_1840_;
                    } else {
                        let mut v___x_1841_: u8 = 0;
                        let mut v_b_u2080_1842_: u8 = 0;
                        let mut v___x_1843_: u8 = 0;
                        let mut v_b_u2081_1844_: u8 = 0;
                        let mut v___x_1845_: u32 = 0;
                        let mut v___x_1846_: u32 = 0;
                        let mut v___x_1847_: u32 = 0;
                        let mut v___x_1848_: u32 = 0;
                        let mut v_r_1849_: u32 = 0;
                        let mut v___x_1850_: u32 = 0;
                        let mut v___x_1851_: u8 = 0;
                        v___x_1841_ = 31;
                        v_b_u2080_1842_ = lean_uint8_land(v___x_1730_, v___x_1841_);
                        v___x_1843_ = 63;
                        v_b_u2081_1844_ = lean_uint8_land(v___x_1837_, v___x_1843_);
                        v___x_1845_ = lean_uint8_to_uint32(v_b_u2080_1842_);
                        v___x_1846_ = 6;
                        v___x_1847_ = lean_uint32_shift_left(v___x_1845_, v___x_1846_);
                        v___x_1848_ = lean_uint8_to_uint32(v_b_u2081_1844_);
                        v_r_1849_ = lean_uint32_lor(v___x_1847_, v___x_1848_);
                        v___x_1850_ = 128;
                        v___x_1851_ = lean_uint32_dec_lt(v_r_1849_, v___x_1850_);
                        if v___x_1851_ == 0 {
                            let mut v___x_1852_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1853_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_1852_ = crate::leanh::lean_box_uint32(v_r_1849_);
                            v___x_1853_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1853_, 0, v___x_1852_);
                            return v___x_1853_;
                        } else {
                            let mut v___x_1854_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_1854_ = crate::leanh::lean_box(0);
                            return v___x_1854_;
                        }
                    }
                }
            }
        } else {
            let mut v___x_1855_: u32 = 0;
            let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1855_ = lean_uint8_to_uint32(v___x_1730_);
            v___x_1856_ = crate::leanh::lean_box_uint32(v___x_1855_);
            v___x_1857_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1857_, 0, v___x_1856_);
            return v___x_1857_;
        }
    }
}
pub unsafe fn l_ByteArray_utf8DecodeChar_x3f___boxed(
    mut v_bytes_1858_: *mut crate::leanh::LeanObject,
    mut v_i_1859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1860_ = l_ByteArray_utf8DecodeChar_x3f(v_bytes_1858_, v_i_1859_);
    crate::leanh::lean_dec(v_i_1859_);
    crate::leanh::lean_dec_ref(v_bytes_1858_);
    return v_res_1860_;
}
pub unsafe fn l_ByteArray_validateUTF8At(
    mut v_bytes_1861_: *mut crate::leanh::LeanObject,
    mut v_i_1862_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: u8 = 0;
    v___x_1863_ = lean_byte_array_size(v_bytes_1861_);
    v___x_1864_ = lean_nat_dec_lt(v_i_1862_, v___x_1863_);
    if v___x_1864_ == 0 {
        return v___x_1864_;
    } else {
        let mut v___x_1865_: u8 = 0;
        let mut v___x_1866_: u8 = 0;
        let mut v___x_1867_: u8 = 0;
        let mut v___x_1868_: u8 = 0;
        let mut v___x_1869_: u8 = 0;
        v___x_1865_ = lean_byte_array_fget(v_bytes_1861_, v_i_1862_);
        v___x_1866_ = 128;
        v___x_1867_ = lean_uint8_land(v___x_1865_, v___x_1866_);
        v___x_1868_ = 0;
        v___x_1869_ = lean_uint8_dec_eq(v___x_1867_, v___x_1868_);
        if v___x_1869_ == 0 {
            let mut v___x_1870_: u8 = 0;
            let mut v___x_1871_: u8 = 0;
            let mut v___x_1872_: u8 = 0;
            let mut v___x_1873_: u8 = 0;
            v___x_1870_ = 224;
            v___x_1871_ = lean_uint8_land(v___x_1865_, v___x_1870_);
            v___x_1872_ = 192;
            v___x_1873_ = lean_uint8_dec_eq(v___x_1871_, v___x_1872_);
            if v___x_1873_ == 0 {
                let mut v___x_1874_: u8 = 0;
                let mut v___x_1875_: u8 = 0;
                let mut v___x_1876_: u8 = 0;
                v___x_1874_ = 240;
                v___x_1875_ = lean_uint8_land(v___x_1865_, v___x_1874_);
                v___x_1876_ = lean_uint8_dec_eq(v___x_1875_, v___x_1870_);
                if v___x_1876_ == 0 {
                    let mut v___x_1877_: u8 = 0;
                    let mut v___x_1878_: u8 = 0;
                    let mut v___x_1879_: u8 = 0;
                    v___x_1877_ = 248;
                    v___x_1878_ = lean_uint8_land(v___x_1865_, v___x_1877_);
                    v___x_1879_ = lean_uint8_dec_eq(v___x_1878_, v___x_1874_);
                    if v___x_1879_ == 0 {
                        return v___x_1879_;
                    } else {
                        let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1882_: u8 = 0;
                        v___x_1880_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_1881_ = lean_nat_add(v_i_1862_, v___x_1880_);
                        v___x_1882_ = lean_nat_dec_lt(v___x_1881_, v___x_1863_);
                        if v___x_1882_ == 0 {
                            crate::leanh::lean_dec(v___x_1881_);
                            return v___x_1876_;
                        } else {
                            let mut v___x_1883_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1884_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1885_: u8 = 0;
                            let mut v___x_1886_: u8 = 0;
                            let mut v___x_1887_: u8 = 0;
                            v___x_1883_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1884_ = lean_nat_add(v_i_1862_, v___x_1883_);
                            v___x_1885_ = lean_byte_array_fget(v_bytes_1861_, v___x_1884_);
                            crate::leanh::lean_dec(v___x_1884_);
                            v___x_1886_ = lean_uint8_land(v___x_1885_, v___x_1872_);
                            v___x_1887_ = lean_uint8_dec_eq(v___x_1886_, v___x_1866_);
                            if v___x_1887_ == 0 {
                                crate::leanh::lean_dec(v___x_1881_);
                                return v___x_1887_;
                            } else {
                                let mut v___x_1888_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1889_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1890_: u8 = 0;
                                let mut v___x_1891_: u8 = 0;
                                let mut v___x_1892_: u8 = 0;
                                v___x_1888_ = crate::leanh::lean_unsigned_to_nat(2);
                                v___x_1889_ = lean_nat_add(v_i_1862_, v___x_1888_);
                                v___x_1890_ = lean_byte_array_fget(v_bytes_1861_, v___x_1889_);
                                crate::leanh::lean_dec(v___x_1889_);
                                v___x_1891_ = lean_uint8_land(v___x_1890_, v___x_1872_);
                                v___x_1892_ = lean_uint8_dec_eq(v___x_1891_, v___x_1866_);
                                if v___x_1892_ == 0 {
                                    crate::leanh::lean_dec(v___x_1881_);
                                    return v___x_1892_;
                                } else {
                                    let mut v___x_1893_: u8 = 0;
                                    let mut v___x_1894_: u8 = 0;
                                    let mut v___x_1895_: u8 = 0;
                                    v___x_1893_ = lean_byte_array_fget(v_bytes_1861_, v___x_1881_);
                                    crate::leanh::lean_dec(v___x_1881_);
                                    v___x_1894_ = lean_uint8_land(v___x_1893_, v___x_1872_);
                                    v___x_1895_ = lean_uint8_dec_eq(v___x_1894_, v___x_1866_);
                                    if v___x_1895_ == 0 {
                                        return v___x_1895_;
                                    } else {
                                        let mut v___x_1896_: u8 = 0;
                                        let mut v_b_u2080_1897_: u8 = 0;
                                        let mut v___x_1898_: u8 = 0;
                                        let mut v_b_u2081_1899_: u8 = 0;
                                        let mut v_b_u2082_1900_: u8 = 0;
                                        let mut v_b_u2083_1901_: u8 = 0;
                                        let mut v___x_1902_: u32 = 0;
                                        let mut v___x_1903_: u32 = 0;
                                        let mut v___x_1904_: u32 = 0;
                                        let mut v___x_1905_: u32 = 0;
                                        let mut v___x_1906_: u32 = 0;
                                        let mut v___x_1907_: u32 = 0;
                                        let mut v___x_1908_: u32 = 0;
                                        let mut v___x_1909_: u32 = 0;
                                        let mut v___x_1910_: u32 = 0;
                                        let mut v___x_1911_: u32 = 0;
                                        let mut v___x_1912_: u32 = 0;
                                        let mut v___x_1913_: u32 = 0;
                                        let mut v_r_1914_: u32 = 0;
                                        let mut v___x_1915_: u32 = 0;
                                        let mut v___x_1916_: u8 = 0;
                                        v___x_1896_ = 7;
                                        v_b_u2080_1897_ = lean_uint8_land(v___x_1865_, v___x_1896_);
                                        v___x_1898_ = 63;
                                        v_b_u2081_1899_ = lean_uint8_land(v___x_1885_, v___x_1898_);
                                        v_b_u2082_1900_ = lean_uint8_land(v___x_1890_, v___x_1898_);
                                        v_b_u2083_1901_ = lean_uint8_land(v___x_1893_, v___x_1898_);
                                        v___x_1902_ = lean_uint8_to_uint32(v_b_u2080_1897_);
                                        v___x_1903_ = 18;
                                        v___x_1904_ =
                                            lean_uint32_shift_left(v___x_1902_, v___x_1903_);
                                        v___x_1905_ = lean_uint8_to_uint32(v_b_u2081_1899_);
                                        v___x_1906_ = 12;
                                        v___x_1907_ =
                                            lean_uint32_shift_left(v___x_1905_, v___x_1906_);
                                        v___x_1908_ = lean_uint32_lor(v___x_1904_, v___x_1907_);
                                        v___x_1909_ = lean_uint8_to_uint32(v_b_u2082_1900_);
                                        v___x_1910_ = 6;
                                        v___x_1911_ =
                                            lean_uint32_shift_left(v___x_1909_, v___x_1910_);
                                        v___x_1912_ = lean_uint32_lor(v___x_1908_, v___x_1911_);
                                        v___x_1913_ = lean_uint8_to_uint32(v_b_u2083_1901_);
                                        v_r_1914_ = lean_uint32_lor(v___x_1912_, v___x_1913_);
                                        v___x_1915_ = 65536;
                                        v___x_1916_ = lean_uint32_dec_le(v___x_1915_, v_r_1914_);
                                        if v___x_1916_ == 0 {
                                            return v___x_1876_;
                                        } else {
                                            let mut v___x_1917_: u32 = 0;
                                            let mut v___x_1918_: u8 = 0;
                                            v___x_1917_ = 1114111;
                                            v___x_1918_ =
                                                lean_uint32_dec_le(v_r_1914_, v___x_1917_);
                                            if v___x_1918_ == 0 {
                                                return v___x_1876_;
                                            } else {
                                                return v___x_1895_;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1921_: u8 = 0;
                    v___x_1919_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_1920_ = lean_nat_add(v_i_1862_, v___x_1919_);
                    v___x_1921_ = lean_nat_dec_lt(v___x_1920_, v___x_1863_);
                    if v___x_1921_ == 0 {
                        crate::leanh::lean_dec(v___x_1920_);
                        return v___x_1873_;
                    } else {
                        let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1924_: u8 = 0;
                        let mut v___x_1925_: u8 = 0;
                        let mut v___x_1926_: u8 = 0;
                        v___x_1922_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1923_ = lean_nat_add(v_i_1862_, v___x_1922_);
                        v___x_1924_ = lean_byte_array_fget(v_bytes_1861_, v___x_1923_);
                        crate::leanh::lean_dec(v___x_1923_);
                        v___x_1925_ = lean_uint8_land(v___x_1924_, v___x_1872_);
                        v___x_1926_ = lean_uint8_dec_eq(v___x_1925_, v___x_1866_);
                        if v___x_1926_ == 0 {
                            crate::leanh::lean_dec(v___x_1920_);
                            return v___x_1926_;
                        } else {
                            let mut v___x_1927_: u8 = 0;
                            let mut v___x_1928_: u8 = 0;
                            let mut v___x_1929_: u8 = 0;
                            v___x_1927_ = lean_byte_array_fget(v_bytes_1861_, v___x_1920_);
                            crate::leanh::lean_dec(v___x_1920_);
                            v___x_1928_ = lean_uint8_land(v___x_1927_, v___x_1872_);
                            v___x_1929_ = lean_uint8_dec_eq(v___x_1928_, v___x_1866_);
                            if v___x_1929_ == 0 {
                                return v___x_1929_;
                            } else {
                                let mut v___x_1930_: u8 = 0;
                                let mut v_b_u2080_1931_: u8 = 0;
                                let mut v___x_1932_: u8 = 0;
                                let mut v_b_u2081_1933_: u8 = 0;
                                let mut v_b_u2082_1934_: u8 = 0;
                                let mut v___x_1935_: u32 = 0;
                                let mut v___x_1936_: u32 = 0;
                                let mut v___x_1937_: u32 = 0;
                                let mut v___x_1938_: u32 = 0;
                                let mut v___x_1939_: u32 = 0;
                                let mut v___x_1940_: u32 = 0;
                                let mut v___x_1941_: u32 = 0;
                                let mut v___x_1942_: u32 = 0;
                                let mut v_r_1943_: u32 = 0;
                                let mut v___x_1944_: u32 = 0;
                                let mut v___x_1945_: u8 = 0;
                                v___x_1930_ = 15;
                                v_b_u2080_1931_ = lean_uint8_land(v___x_1865_, v___x_1930_);
                                v___x_1932_ = 63;
                                v_b_u2081_1933_ = lean_uint8_land(v___x_1924_, v___x_1932_);
                                v_b_u2082_1934_ = lean_uint8_land(v___x_1927_, v___x_1932_);
                                v___x_1935_ = lean_uint8_to_uint32(v_b_u2080_1931_);
                                v___x_1936_ = 12;
                                v___x_1937_ = lean_uint32_shift_left(v___x_1935_, v___x_1936_);
                                v___x_1938_ = lean_uint8_to_uint32(v_b_u2081_1933_);
                                v___x_1939_ = 6;
                                v___x_1940_ = lean_uint32_shift_left(v___x_1938_, v___x_1939_);
                                v___x_1941_ = lean_uint32_lor(v___x_1937_, v___x_1940_);
                                v___x_1942_ = lean_uint8_to_uint32(v_b_u2082_1934_);
                                v_r_1943_ = lean_uint32_lor(v___x_1941_, v___x_1942_);
                                v___x_1944_ = 2048;
                                v___x_1945_ = lean_uint32_dec_le(v___x_1944_, v_r_1943_);
                                if v___x_1945_ == 0 {
                                    return v___x_1873_;
                                } else {
                                    let mut v___x_1946_: u32 = 0;
                                    let mut v___x_1947_: u8 = 0;
                                    v___x_1946_ = 55296;
                                    v___x_1947_ = lean_uint32_dec_lt(v_r_1943_, v___x_1946_);
                                    if v___x_1947_ == 0 {
                                        let mut v___x_1948_: u32 = 0;
                                        let mut v___x_1949_: u8 = 0;
                                        v___x_1948_ = 57343;
                                        v___x_1949_ = lean_uint32_dec_lt(v___x_1948_, v_r_1943_);
                                        if v___x_1949_ == 0 {
                                            return v___x_1873_;
                                        } else {
                                            return v___x_1929_;
                                        }
                                    } else {
                                        return v___x_1929_;
                                    }
                                }
                            }
                        }
                    }
                }
            } else {
                let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1952_: u8 = 0;
                v___x_1950_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1951_ = lean_nat_add(v_i_1862_, v___x_1950_);
                v___x_1952_ = lean_nat_dec_lt(v___x_1951_, v___x_1863_);
                if v___x_1952_ == 0 {
                    crate::leanh::lean_dec(v___x_1951_);
                    return v___x_1869_;
                } else {
                    let mut v___x_1953_: u8 = 0;
                    let mut v___x_1954_: u8 = 0;
                    let mut v___x_1955_: u8 = 0;
                    v___x_1953_ = lean_byte_array_fget(v_bytes_1861_, v___x_1951_);
                    crate::leanh::lean_dec(v___x_1951_);
                    v___x_1954_ = lean_uint8_land(v___x_1953_, v___x_1872_);
                    v___x_1955_ = lean_uint8_dec_eq(v___x_1954_, v___x_1866_);
                    if v___x_1955_ == 0 {
                        return v___x_1955_;
                    } else {
                        let mut v___x_1956_: u8 = 0;
                        let mut v_b_u2080_1957_: u8 = 0;
                        let mut v___x_1958_: u8 = 0;
                        let mut v_b_u2081_1959_: u8 = 0;
                        let mut v___x_1960_: u32 = 0;
                        let mut v___x_1961_: u32 = 0;
                        let mut v___x_1962_: u32 = 0;
                        let mut v___x_1963_: u32 = 0;
                        let mut v_r_1964_: u32 = 0;
                        let mut v___x_1965_: u32 = 0;
                        let mut v___x_1966_: u8 = 0;
                        v___x_1956_ = 31;
                        v_b_u2080_1957_ = lean_uint8_land(v___x_1865_, v___x_1956_);
                        v___x_1958_ = 63;
                        v_b_u2081_1959_ = lean_uint8_land(v___x_1953_, v___x_1958_);
                        v___x_1960_ = lean_uint8_to_uint32(v_b_u2080_1957_);
                        v___x_1961_ = 6;
                        v___x_1962_ = lean_uint32_shift_left(v___x_1960_, v___x_1961_);
                        v___x_1963_ = lean_uint8_to_uint32(v_b_u2081_1959_);
                        v_r_1964_ = lean_uint32_lor(v___x_1962_, v___x_1963_);
                        v___x_1965_ = 128;
                        v___x_1966_ = lean_uint32_dec_le(v___x_1965_, v_r_1964_);
                        return v___x_1966_;
                    }
                }
            }
        } else {
            return v___x_1869_;
        }
    }
}
pub unsafe fn l_ByteArray_validateUTF8At___boxed(
    mut v_bytes_1967_: *mut crate::leanh::LeanObject,
    mut v_i_1968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1969_: u8 = 0;
    let mut v_r_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1969_ = l_ByteArray_validateUTF8At(v_bytes_1967_, v_i_1968_);
    crate::leanh::lean_dec(v_i_1968_);
    crate::leanh::lean_dec_ref(v_bytes_1967_);
    v_r_1970_ = crate::leanh::lean_box((v_res_1969_) as usize);
    return v_r_1970_;
}
pub unsafe fn l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(
    mut v_x_1971_: u8,
    mut v_h__1_1972_: *mut crate::leanh::LeanObject,
    mut v_h__2_1973_: *mut crate::leanh::LeanObject,
    mut v_h__3_1974_: *mut crate::leanh::LeanObject,
    mut v_h__4_1975_: *mut crate::leanh::LeanObject,
    mut v_h__5_1976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_1971_ {
        0 => {
            let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1976_);
            crate::leanh::lean_dec(v_h__4_1975_);
            crate::leanh::lean_dec(v_h__3_1974_);
            crate::leanh::lean_dec(v_h__2_1973_);
            v___x_1977_ = crate::leanh::lean_apply_1(v_h__1_1972_, crate::leanh::lean_box(0));
            return v___x_1977_;
        }
        1 => {
            let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1976_);
            crate::leanh::lean_dec(v_h__4_1975_);
            crate::leanh::lean_dec(v_h__3_1974_);
            crate::leanh::lean_dec(v_h__1_1972_);
            v___x_1978_ = crate::leanh::lean_apply_1(v_h__2_1973_, crate::leanh::lean_box(0));
            return v___x_1978_;
        }
        2 => {
            let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1976_);
            crate::leanh::lean_dec(v_h__4_1975_);
            crate::leanh::lean_dec(v_h__2_1973_);
            crate::leanh::lean_dec(v_h__1_1972_);
            v___x_1979_ = crate::leanh::lean_apply_1(v_h__3_1974_, crate::leanh::lean_box(0));
            return v___x_1979_;
        }
        3 => {
            let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1976_);
            crate::leanh::lean_dec(v_h__3_1974_);
            crate::leanh::lean_dec(v_h__2_1973_);
            crate::leanh::lean_dec(v_h__1_1972_);
            v___x_1980_ = crate::leanh::lean_apply_1(v_h__4_1975_, crate::leanh::lean_box(0));
            return v___x_1980_;
        }
        _ => {
            let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1975_);
            crate::leanh::lean_dec(v_h__3_1974_);
            crate::leanh::lean_dec(v_h__2_1973_);
            crate::leanh::lean_dec(v_h__1_1972_);
            v___x_1981_ = crate::leanh::lean_apply_1(v_h__5_1976_, crate::leanh::lean_box(0));
            return v___x_1981_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg___boxed(
    mut v_x_1982_: *mut crate::leanh::LeanObject,
    mut v_h__1_1983_: *mut crate::leanh::LeanObject,
    mut v_h__2_1984_: *mut crate::leanh::LeanObject,
    mut v_h__3_1985_: *mut crate::leanh::LeanObject,
    mut v_h__4_1986_: *mut crate::leanh::LeanObject,
    mut v_h__5_1987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_47__boxed_1988_: u8 = 0;
    let mut v_res_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_47__boxed_1988_ = (crate::leanh::lean_unbox(v_x_1982_) as u8);
    v_res_1989_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___redArg(v_x_47__boxed_1988_, v_h__1_1983_, v_h__2_1984_, v_h__3_1985_, v_h__4_1986_, v_h__5_1987_);
    return v_res_1989_;
}
pub unsafe fn l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(
    mut v_motive_1990_: *mut crate::leanh::LeanObject,
    mut v_x_1991_: u8,
    mut v_h__1_1992_: *mut crate::leanh::LeanObject,
    mut v_h__2_1993_: *mut crate::leanh::LeanObject,
    mut v_h__3_1994_: *mut crate::leanh::LeanObject,
    mut v_h__4_1995_: *mut crate::leanh::LeanObject,
    mut v_h__5_1996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_1991_ {
        0 => {
            let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1996_);
            crate::leanh::lean_dec(v_h__4_1995_);
            crate::leanh::lean_dec(v_h__3_1994_);
            crate::leanh::lean_dec(v_h__2_1993_);
            v___x_1997_ = crate::leanh::lean_apply_1(v_h__1_1992_, crate::leanh::lean_box(0));
            return v___x_1997_;
        }
        1 => {
            let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1996_);
            crate::leanh::lean_dec(v_h__4_1995_);
            crate::leanh::lean_dec(v_h__3_1994_);
            crate::leanh::lean_dec(v_h__1_1992_);
            v___x_1998_ = crate::leanh::lean_apply_1(v_h__2_1993_, crate::leanh::lean_box(0));
            return v___x_1998_;
        }
        2 => {
            let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1996_);
            crate::leanh::lean_dec(v_h__4_1995_);
            crate::leanh::lean_dec(v_h__2_1993_);
            crate::leanh::lean_dec(v_h__1_1992_);
            v___x_1999_ = crate::leanh::lean_apply_1(v_h__3_1994_, crate::leanh::lean_box(0));
            return v___x_1999_;
        }
        3 => {
            let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1996_);
            crate::leanh::lean_dec(v_h__3_1994_);
            crate::leanh::lean_dec(v_h__2_1993_);
            crate::leanh::lean_dec(v_h__1_1992_);
            v___x_2000_ = crate::leanh::lean_apply_1(v_h__4_1995_, crate::leanh::lean_box(0));
            return v___x_2000_;
        }
        _ => {
            let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1995_);
            crate::leanh::lean_dec(v_h__3_1994_);
            crate::leanh::lean_dec(v_h__2_1993_);
            crate::leanh::lean_dec(v_h__1_1992_);
            v___x_2001_ = crate::leanh::lean_apply_1(v_h__5_1996_, crate::leanh::lean_box(0));
            return v___x_2001_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter___boxed(
    mut v_motive_2002_: *mut crate::leanh::LeanObject,
    mut v_x_2003_: *mut crate::leanh::LeanObject,
    mut v_h__1_2004_: *mut crate::leanh::LeanObject,
    mut v_h__2_2005_: *mut crate::leanh::LeanObject,
    mut v_h__3_2006_: *mut crate::leanh::LeanObject,
    mut v_h__4_2007_: *mut crate::leanh::LeanObject,
    mut v_h__5_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_60__boxed_2009_: u8 = 0;
    let mut v_res_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_60__boxed_2009_ = (crate::leanh::lean_unbox(v_x_2003_) as u8);
    v_res_2010_ =
        l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_match__1_splitter(
            v_motive_2002_,
            v_x_60__boxed_2009_,
            v_h__1_2004_,
            v_h__2_2005_,
            v_h__3_2006_,
            v_h__4_2007_,
            v_h__5_2008_,
        );
    return v_res_2010_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar___redArg(
    mut v_bytes_2011_: *mut crate::leanh::LeanObject,
    mut v_i_2012_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: u8 = 0;
    let mut v___x_2015_: u8 = 0;
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: u8 = 0;
    let mut v___x_2018_: u8 = 0;
    let mut v___x_2019_: u8 = 0;
    v___x_2013_ = lean_byte_array_size(v_bytes_2011_);
    v___x_2014_ = lean_nat_dec_lt(v_i_2012_, v___x_2013_);
    v___x_2015_ = lean_byte_array_fget(v_bytes_2011_, v_i_2012_);
    v___x_2016_ = 128;
    v___x_2017_ = lean_uint8_land(v___x_2015_, v___x_2016_);
    v___x_2018_ = 0;
    v___x_2019_ = lean_uint8_dec_eq(v___x_2017_, v___x_2018_);
    if v___x_2019_ == 0 {
        let mut v___x_2020_: u8 = 0;
        let mut v___x_2021_: u8 = 0;
        let mut v___x_2022_: u8 = 0;
        let mut v___x_2023_: u8 = 0;
        v___x_2020_ = 224;
        v___x_2021_ = lean_uint8_land(v___x_2015_, v___x_2020_);
        v___x_2022_ = 192;
        v___x_2023_ = lean_uint8_dec_eq(v___x_2021_, v___x_2022_);
        if v___x_2023_ == 0 {
            let mut v___x_2024_: u8 = 0;
            let mut v___x_2025_: u8 = 0;
            let mut v___x_2026_: u8 = 0;
            v___x_2024_ = 240;
            v___x_2025_ = lean_uint8_land(v___x_2015_, v___x_2024_);
            v___x_2026_ = lean_uint8_dec_eq(v___x_2025_, v___x_2020_);
            if v___x_2026_ == 0 {
                let mut v___x_2027_: u8 = 0;
                let mut v___x_2028_: u8 = 0;
                let mut v___x_2029_: u8 = 0;
                let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2032_: u8 = 0;
                let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2035_: u8 = 0;
                let mut v___x_2036_: u8 = 0;
                let mut v___x_2037_: u8 = 0;
                let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2040_: u8 = 0;
                let mut v___x_2041_: u8 = 0;
                let mut v___x_2042_: u8 = 0;
                let mut v___x_2043_: u8 = 0;
                let mut v___x_2044_: u8 = 0;
                let mut v___x_2045_: u8 = 0;
                let mut v___x_2046_: u8 = 0;
                let mut v_b_u2080_2047_: u8 = 0;
                let mut v___x_2048_: u8 = 0;
                let mut v_b_u2081_2049_: u8 = 0;
                let mut v_b_u2082_2050_: u8 = 0;
                let mut v_b_u2083_2051_: u8 = 0;
                let mut v___x_2052_: u32 = 0;
                let mut v___x_2053_: u32 = 0;
                let mut v___x_2054_: u32 = 0;
                let mut v___x_2055_: u32 = 0;
                let mut v___x_2056_: u32 = 0;
                let mut v___x_2057_: u32 = 0;
                let mut v___x_2058_: u32 = 0;
                let mut v___x_2059_: u32 = 0;
                let mut v___x_2060_: u32 = 0;
                let mut v___x_2061_: u32 = 0;
                let mut v___x_2062_: u32 = 0;
                let mut v___x_2063_: u32 = 0;
                let mut v_r_2064_: u32 = 0;
                let mut v___x_2065_: u32 = 0;
                let mut v___x_2066_: u8 = 0;
                let mut v___x_2067_: u32 = 0;
                let mut v___x_2068_: u8 = 0;
                v___x_2027_ = 248;
                v___x_2028_ = lean_uint8_land(v___x_2015_, v___x_2027_);
                v___x_2029_ = lean_uint8_dec_eq(v___x_2028_, v___x_2024_);
                v___x_2030_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2031_ = lean_nat_add(v_i_2012_, v___x_2030_);
                v___x_2032_ = lean_nat_dec_lt(v___x_2031_, v___x_2013_);
                v___x_2033_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2034_ = lean_nat_add(v_i_2012_, v___x_2033_);
                v___x_2035_ = lean_byte_array_fget(v_bytes_2011_, v___x_2034_);
                crate::leanh::lean_dec(v___x_2034_);
                v___x_2036_ = lean_uint8_land(v___x_2035_, v___x_2022_);
                v___x_2037_ = lean_uint8_dec_eq(v___x_2036_, v___x_2016_);
                v___x_2038_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2039_ = lean_nat_add(v_i_2012_, v___x_2038_);
                v___x_2040_ = lean_byte_array_fget(v_bytes_2011_, v___x_2039_);
                crate::leanh::lean_dec(v___x_2039_);
                v___x_2041_ = lean_uint8_land(v___x_2040_, v___x_2022_);
                v___x_2042_ = lean_uint8_dec_eq(v___x_2041_, v___x_2016_);
                v___x_2043_ = lean_byte_array_fget(v_bytes_2011_, v___x_2031_);
                crate::leanh::lean_dec(v___x_2031_);
                v___x_2044_ = lean_uint8_land(v___x_2043_, v___x_2022_);
                v___x_2045_ = lean_uint8_dec_eq(v___x_2044_, v___x_2016_);
                v___x_2046_ = 7;
                v_b_u2080_2047_ = lean_uint8_land(v___x_2015_, v___x_2046_);
                v___x_2048_ = 63;
                v_b_u2081_2049_ = lean_uint8_land(v___x_2035_, v___x_2048_);
                v_b_u2082_2050_ = lean_uint8_land(v___x_2040_, v___x_2048_);
                v_b_u2083_2051_ = lean_uint8_land(v___x_2043_, v___x_2048_);
                v___x_2052_ = lean_uint8_to_uint32(v_b_u2080_2047_);
                v___x_2053_ = 18;
                v___x_2054_ = lean_uint32_shift_left(v___x_2052_, v___x_2053_);
                v___x_2055_ = lean_uint8_to_uint32(v_b_u2081_2049_);
                v___x_2056_ = 12;
                v___x_2057_ = lean_uint32_shift_left(v___x_2055_, v___x_2056_);
                v___x_2058_ = lean_uint32_lor(v___x_2054_, v___x_2057_);
                v___x_2059_ = lean_uint8_to_uint32(v_b_u2082_2050_);
                v___x_2060_ = 6;
                v___x_2061_ = lean_uint32_shift_left(v___x_2059_, v___x_2060_);
                v___x_2062_ = lean_uint32_lor(v___x_2058_, v___x_2061_);
                v___x_2063_ = lean_uint8_to_uint32(v_b_u2083_2051_);
                v_r_2064_ = lean_uint32_lor(v___x_2062_, v___x_2063_);
                v___x_2065_ = 65536;
                v___x_2066_ = lean_uint32_dec_lt(v_r_2064_, v___x_2065_);
                v___x_2067_ = 1114111;
                v___x_2068_ = lean_uint32_dec_lt(v___x_2067_, v_r_2064_);
                return v_r_2064_;
            } else {
                let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2071_: u8 = 0;
                let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2074_: u8 = 0;
                let mut v___x_2075_: u8 = 0;
                let mut v___x_2076_: u8 = 0;
                let mut v___x_2077_: u8 = 0;
                let mut v___x_2078_: u8 = 0;
                let mut v___x_2079_: u8 = 0;
                let mut v___x_2080_: u8 = 0;
                let mut v_b_u2080_2081_: u8 = 0;
                let mut v___x_2082_: u8 = 0;
                let mut v_b_u2081_2083_: u8 = 0;
                let mut v_b_u2082_2084_: u8 = 0;
                let mut v___x_2085_: u32 = 0;
                let mut v___x_2086_: u32 = 0;
                let mut v___x_2087_: u32 = 0;
                let mut v___x_2088_: u32 = 0;
                let mut v___x_2089_: u32 = 0;
                let mut v___x_2090_: u32 = 0;
                let mut v___x_2091_: u32 = 0;
                let mut v___x_2092_: u32 = 0;
                let mut v_r_2093_: u32 = 0;
                let mut v___x_2094_: u32 = 0;
                let mut v___x_2095_: u8 = 0;
                let mut v___x_2096_: u32 = 0;
                let mut v___x_2097_: u8 = 0;
                v___x_2069_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2070_ = lean_nat_add(v_i_2012_, v___x_2069_);
                v___x_2071_ = lean_nat_dec_lt(v___x_2070_, v___x_2013_);
                v___x_2072_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2073_ = lean_nat_add(v_i_2012_, v___x_2072_);
                v___x_2074_ = lean_byte_array_fget(v_bytes_2011_, v___x_2073_);
                crate::leanh::lean_dec(v___x_2073_);
                v___x_2075_ = lean_uint8_land(v___x_2074_, v___x_2022_);
                v___x_2076_ = lean_uint8_dec_eq(v___x_2075_, v___x_2016_);
                v___x_2077_ = lean_byte_array_fget(v_bytes_2011_, v___x_2070_);
                crate::leanh::lean_dec(v___x_2070_);
                v___x_2078_ = lean_uint8_land(v___x_2077_, v___x_2022_);
                v___x_2079_ = lean_uint8_dec_eq(v___x_2078_, v___x_2016_);
                v___x_2080_ = 15;
                v_b_u2080_2081_ = lean_uint8_land(v___x_2015_, v___x_2080_);
                v___x_2082_ = 63;
                v_b_u2081_2083_ = lean_uint8_land(v___x_2074_, v___x_2082_);
                v_b_u2082_2084_ = lean_uint8_land(v___x_2077_, v___x_2082_);
                v___x_2085_ = lean_uint8_to_uint32(v_b_u2080_2081_);
                v___x_2086_ = 12;
                v___x_2087_ = lean_uint32_shift_left(v___x_2085_, v___x_2086_);
                v___x_2088_ = lean_uint8_to_uint32(v_b_u2081_2083_);
                v___x_2089_ = 6;
                v___x_2090_ = lean_uint32_shift_left(v___x_2088_, v___x_2089_);
                v___x_2091_ = lean_uint32_lor(v___x_2087_, v___x_2090_);
                v___x_2092_ = lean_uint8_to_uint32(v_b_u2082_2084_);
                v_r_2093_ = lean_uint32_lor(v___x_2091_, v___x_2092_);
                v___x_2094_ = 2048;
                v___x_2095_ = lean_uint32_dec_lt(v_r_2093_, v___x_2094_);
                v___x_2096_ = 55296;
                v___x_2097_ = lean_uint32_dec_le(v___x_2096_, v_r_2093_);
                if v___x_2097_ == 0 {
                    return v_r_2093_;
                } else {
                    let mut v___x_2098_: u32 = 0;
                    let mut v___x_2099_: u8 = 0;
                    v___x_2098_ = 57343;
                    v___x_2099_ = lean_uint32_dec_le(v_r_2093_, v___x_2098_);
                    return v_r_2093_;
                }
            }
        } else {
            let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2102_: u8 = 0;
            let mut v___x_2103_: u8 = 0;
            let mut v___x_2104_: u8 = 0;
            let mut v___x_2105_: u8 = 0;
            let mut v___x_2106_: u8 = 0;
            let mut v_b_u2080_2107_: u8 = 0;
            let mut v___x_2108_: u8 = 0;
            let mut v_b_u2081_2109_: u8 = 0;
            let mut v___x_2110_: u32 = 0;
            let mut v___x_2111_: u32 = 0;
            let mut v___x_2112_: u32 = 0;
            let mut v___x_2113_: u32 = 0;
            let mut v_r_2114_: u32 = 0;
            let mut v___x_2115_: u32 = 0;
            let mut v___x_2116_: u8 = 0;
            v___x_2100_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_2101_ = lean_nat_add(v_i_2012_, v___x_2100_);
            v___x_2102_ = lean_nat_dec_lt(v___x_2101_, v___x_2013_);
            v___x_2103_ = lean_byte_array_fget(v_bytes_2011_, v___x_2101_);
            crate::leanh::lean_dec(v___x_2101_);
            v___x_2104_ = lean_uint8_land(v___x_2103_, v___x_2022_);
            v___x_2105_ = lean_uint8_dec_eq(v___x_2104_, v___x_2016_);
            v___x_2106_ = 31;
            v_b_u2080_2107_ = lean_uint8_land(v___x_2015_, v___x_2106_);
            v___x_2108_ = 63;
            v_b_u2081_2109_ = lean_uint8_land(v___x_2103_, v___x_2108_);
            v___x_2110_ = lean_uint8_to_uint32(v_b_u2080_2107_);
            v___x_2111_ = 6;
            v___x_2112_ = lean_uint32_shift_left(v___x_2110_, v___x_2111_);
            v___x_2113_ = lean_uint8_to_uint32(v_b_u2081_2109_);
            v_r_2114_ = lean_uint32_lor(v___x_2112_, v___x_2113_);
            v___x_2115_ = 128;
            v___x_2116_ = lean_uint32_dec_lt(v_r_2114_, v___x_2115_);
            return v_r_2114_;
        }
    } else {
        let mut v___x_2117_: u32 = 0;
        v___x_2117_ = lean_uint8_to_uint32(v___x_2015_);
        return v___x_2117_;
    }
}
pub unsafe fn l_ByteArray_utf8DecodeChar___redArg___boxed(
    mut v_bytes_2118_: *mut crate::leanh::LeanObject,
    mut v_i_2119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2120_: u32 = 0;
    let mut v_r_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2120_ = l_ByteArray_utf8DecodeChar___redArg(v_bytes_2118_, v_i_2119_);
    crate::leanh::lean_dec(v_i_2119_);
    crate::leanh::lean_dec_ref(v_bytes_2118_);
    v_r_2121_ = crate::leanh::lean_box_uint32(v_res_2120_);
    return v_r_2121_;
}
pub unsafe fn l_ByteArray_utf8DecodeChar(
    mut v_bytes_2122_: *mut crate::leanh::LeanObject,
    mut v_i_2123_: *mut crate::leanh::LeanObject,
    mut v_h_2124_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: u8 = 0;
    let mut v___x_2127_: u8 = 0;
    let mut v___x_2128_: u8 = 0;
    let mut v___x_2129_: u8 = 0;
    let mut v___x_2130_: u8 = 0;
    let mut v___x_2131_: u8 = 0;
    v___x_2125_ = lean_byte_array_size(v_bytes_2122_);
    v___x_2126_ = lean_nat_dec_lt(v_i_2123_, v___x_2125_);
    v___x_2127_ = lean_byte_array_fget(v_bytes_2122_, v_i_2123_);
    v___x_2128_ = 128;
    v___x_2129_ = lean_uint8_land(v___x_2127_, v___x_2128_);
    v___x_2130_ = 0;
    v___x_2131_ = lean_uint8_dec_eq(v___x_2129_, v___x_2130_);
    if v___x_2131_ == 0 {
        let mut v___x_2132_: u8 = 0;
        let mut v___x_2133_: u8 = 0;
        let mut v___x_2134_: u8 = 0;
        let mut v___x_2135_: u8 = 0;
        v___x_2132_ = 224;
        v___x_2133_ = lean_uint8_land(v___x_2127_, v___x_2132_);
        v___x_2134_ = 192;
        v___x_2135_ = lean_uint8_dec_eq(v___x_2133_, v___x_2134_);
        if v___x_2135_ == 0 {
            let mut v___x_2136_: u8 = 0;
            let mut v___x_2137_: u8 = 0;
            let mut v___x_2138_: u8 = 0;
            v___x_2136_ = 240;
            v___x_2137_ = lean_uint8_land(v___x_2127_, v___x_2136_);
            v___x_2138_ = lean_uint8_dec_eq(v___x_2137_, v___x_2132_);
            if v___x_2138_ == 0 {
                let mut v___x_2139_: u8 = 0;
                let mut v___x_2140_: u8 = 0;
                let mut v___x_2141_: u8 = 0;
                let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2144_: u8 = 0;
                let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2147_: u8 = 0;
                let mut v___x_2148_: u8 = 0;
                let mut v___x_2149_: u8 = 0;
                let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2152_: u8 = 0;
                let mut v___x_2153_: u8 = 0;
                let mut v___x_2154_: u8 = 0;
                let mut v___x_2155_: u8 = 0;
                let mut v___x_2156_: u8 = 0;
                let mut v___x_2157_: u8 = 0;
                let mut v___x_2158_: u8 = 0;
                let mut v_b_u2080_2159_: u8 = 0;
                let mut v___x_2160_: u8 = 0;
                let mut v_b_u2081_2161_: u8 = 0;
                let mut v_b_u2082_2162_: u8 = 0;
                let mut v_b_u2083_2163_: u8 = 0;
                let mut v___x_2164_: u32 = 0;
                let mut v___x_2165_: u32 = 0;
                let mut v___x_2166_: u32 = 0;
                let mut v___x_2167_: u32 = 0;
                let mut v___x_2168_: u32 = 0;
                let mut v___x_2169_: u32 = 0;
                let mut v___x_2170_: u32 = 0;
                let mut v___x_2171_: u32 = 0;
                let mut v___x_2172_: u32 = 0;
                let mut v___x_2173_: u32 = 0;
                let mut v___x_2174_: u32 = 0;
                let mut v___x_2175_: u32 = 0;
                let mut v_r_2176_: u32 = 0;
                let mut v___x_2177_: u32 = 0;
                let mut v___x_2178_: u8 = 0;
                let mut v___x_2179_: u32 = 0;
                let mut v___x_2180_: u8 = 0;
                v___x_2139_ = 248;
                v___x_2140_ = lean_uint8_land(v___x_2127_, v___x_2139_);
                v___x_2141_ = lean_uint8_dec_eq(v___x_2140_, v___x_2136_);
                v___x_2142_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2143_ = lean_nat_add(v_i_2123_, v___x_2142_);
                v___x_2144_ = lean_nat_dec_lt(v___x_2143_, v___x_2125_);
                v___x_2145_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2146_ = lean_nat_add(v_i_2123_, v___x_2145_);
                v___x_2147_ = lean_byte_array_fget(v_bytes_2122_, v___x_2146_);
                crate::leanh::lean_dec(v___x_2146_);
                v___x_2148_ = lean_uint8_land(v___x_2147_, v___x_2134_);
                v___x_2149_ = lean_uint8_dec_eq(v___x_2148_, v___x_2128_);
                v___x_2150_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2151_ = lean_nat_add(v_i_2123_, v___x_2150_);
                v___x_2152_ = lean_byte_array_fget(v_bytes_2122_, v___x_2151_);
                crate::leanh::lean_dec(v___x_2151_);
                v___x_2153_ = lean_uint8_land(v___x_2152_, v___x_2134_);
                v___x_2154_ = lean_uint8_dec_eq(v___x_2153_, v___x_2128_);
                v___x_2155_ = lean_byte_array_fget(v_bytes_2122_, v___x_2143_);
                crate::leanh::lean_dec(v___x_2143_);
                v___x_2156_ = lean_uint8_land(v___x_2155_, v___x_2134_);
                v___x_2157_ = lean_uint8_dec_eq(v___x_2156_, v___x_2128_);
                v___x_2158_ = 7;
                v_b_u2080_2159_ = lean_uint8_land(v___x_2127_, v___x_2158_);
                v___x_2160_ = 63;
                v_b_u2081_2161_ = lean_uint8_land(v___x_2147_, v___x_2160_);
                v_b_u2082_2162_ = lean_uint8_land(v___x_2152_, v___x_2160_);
                v_b_u2083_2163_ = lean_uint8_land(v___x_2155_, v___x_2160_);
                v___x_2164_ = lean_uint8_to_uint32(v_b_u2080_2159_);
                v___x_2165_ = 18;
                v___x_2166_ = lean_uint32_shift_left(v___x_2164_, v___x_2165_);
                v___x_2167_ = lean_uint8_to_uint32(v_b_u2081_2161_);
                v___x_2168_ = 12;
                v___x_2169_ = lean_uint32_shift_left(v___x_2167_, v___x_2168_);
                v___x_2170_ = lean_uint32_lor(v___x_2166_, v___x_2169_);
                v___x_2171_ = lean_uint8_to_uint32(v_b_u2082_2162_);
                v___x_2172_ = 6;
                v___x_2173_ = lean_uint32_shift_left(v___x_2171_, v___x_2172_);
                v___x_2174_ = lean_uint32_lor(v___x_2170_, v___x_2173_);
                v___x_2175_ = lean_uint8_to_uint32(v_b_u2083_2163_);
                v_r_2176_ = lean_uint32_lor(v___x_2174_, v___x_2175_);
                v___x_2177_ = 65536;
                v___x_2178_ = lean_uint32_dec_lt(v_r_2176_, v___x_2177_);
                v___x_2179_ = 1114111;
                v___x_2180_ = lean_uint32_dec_lt(v___x_2179_, v_r_2176_);
                return v_r_2176_;
            } else {
                let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2183_: u8 = 0;
                let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2186_: u8 = 0;
                let mut v___x_2187_: u8 = 0;
                let mut v___x_2188_: u8 = 0;
                let mut v___x_2189_: u8 = 0;
                let mut v___x_2190_: u8 = 0;
                let mut v___x_2191_: u8 = 0;
                let mut v___x_2192_: u8 = 0;
                let mut v_b_u2080_2193_: u8 = 0;
                let mut v___x_2194_: u8 = 0;
                let mut v_b_u2081_2195_: u8 = 0;
                let mut v_b_u2082_2196_: u8 = 0;
                let mut v___x_2197_: u32 = 0;
                let mut v___x_2198_: u32 = 0;
                let mut v___x_2199_: u32 = 0;
                let mut v___x_2200_: u32 = 0;
                let mut v___x_2201_: u32 = 0;
                let mut v___x_2202_: u32 = 0;
                let mut v___x_2203_: u32 = 0;
                let mut v___x_2204_: u32 = 0;
                let mut v_r_2205_: u32 = 0;
                let mut v___x_2206_: u32 = 0;
                let mut v___x_2207_: u8 = 0;
                let mut v___x_2208_: u32 = 0;
                let mut v___x_2209_: u8 = 0;
                v___x_2181_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2182_ = lean_nat_add(v_i_2123_, v___x_2181_);
                v___x_2183_ = lean_nat_dec_lt(v___x_2182_, v___x_2125_);
                v___x_2184_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2185_ = lean_nat_add(v_i_2123_, v___x_2184_);
                v___x_2186_ = lean_byte_array_fget(v_bytes_2122_, v___x_2185_);
                crate::leanh::lean_dec(v___x_2185_);
                v___x_2187_ = lean_uint8_land(v___x_2186_, v___x_2134_);
                v___x_2188_ = lean_uint8_dec_eq(v___x_2187_, v___x_2128_);
                v___x_2189_ = lean_byte_array_fget(v_bytes_2122_, v___x_2182_);
                crate::leanh::lean_dec(v___x_2182_);
                v___x_2190_ = lean_uint8_land(v___x_2189_, v___x_2134_);
                v___x_2191_ = lean_uint8_dec_eq(v___x_2190_, v___x_2128_);
                v___x_2192_ = 15;
                v_b_u2080_2193_ = lean_uint8_land(v___x_2127_, v___x_2192_);
                v___x_2194_ = 63;
                v_b_u2081_2195_ = lean_uint8_land(v___x_2186_, v___x_2194_);
                v_b_u2082_2196_ = lean_uint8_land(v___x_2189_, v___x_2194_);
                v___x_2197_ = lean_uint8_to_uint32(v_b_u2080_2193_);
                v___x_2198_ = 12;
                v___x_2199_ = lean_uint32_shift_left(v___x_2197_, v___x_2198_);
                v___x_2200_ = lean_uint8_to_uint32(v_b_u2081_2195_);
                v___x_2201_ = 6;
                v___x_2202_ = lean_uint32_shift_left(v___x_2200_, v___x_2201_);
                v___x_2203_ = lean_uint32_lor(v___x_2199_, v___x_2202_);
                v___x_2204_ = lean_uint8_to_uint32(v_b_u2082_2196_);
                v_r_2205_ = lean_uint32_lor(v___x_2203_, v___x_2204_);
                v___x_2206_ = 2048;
                v___x_2207_ = lean_uint32_dec_lt(v_r_2205_, v___x_2206_);
                v___x_2208_ = 55296;
                v___x_2209_ = lean_uint32_dec_le(v___x_2208_, v_r_2205_);
                if v___x_2209_ == 0 {
                    return v_r_2205_;
                } else {
                    let mut v___x_2210_: u32 = 0;
                    let mut v___x_2211_: u8 = 0;
                    v___x_2210_ = 57343;
                    v___x_2211_ = lean_uint32_dec_le(v_r_2205_, v___x_2210_);
                    return v_r_2205_;
                }
            }
        } else {
            let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2214_: u8 = 0;
            let mut v___x_2215_: u8 = 0;
            let mut v___x_2216_: u8 = 0;
            let mut v___x_2217_: u8 = 0;
            let mut v___x_2218_: u8 = 0;
            let mut v_b_u2080_2219_: u8 = 0;
            let mut v___x_2220_: u8 = 0;
            let mut v_b_u2081_2221_: u8 = 0;
            let mut v___x_2222_: u32 = 0;
            let mut v___x_2223_: u32 = 0;
            let mut v___x_2224_: u32 = 0;
            let mut v___x_2225_: u32 = 0;
            let mut v_r_2226_: u32 = 0;
            let mut v___x_2227_: u32 = 0;
            let mut v___x_2228_: u8 = 0;
            v___x_2212_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_2213_ = lean_nat_add(v_i_2123_, v___x_2212_);
            v___x_2214_ = lean_nat_dec_lt(v___x_2213_, v___x_2125_);
            v___x_2215_ = lean_byte_array_fget(v_bytes_2122_, v___x_2213_);
            crate::leanh::lean_dec(v___x_2213_);
            v___x_2216_ = lean_uint8_land(v___x_2215_, v___x_2134_);
            v___x_2217_ = lean_uint8_dec_eq(v___x_2216_, v___x_2128_);
            v___x_2218_ = 31;
            v_b_u2080_2219_ = lean_uint8_land(v___x_2127_, v___x_2218_);
            v___x_2220_ = 63;
            v_b_u2081_2221_ = lean_uint8_land(v___x_2215_, v___x_2220_);
            v___x_2222_ = lean_uint8_to_uint32(v_b_u2080_2219_);
            v___x_2223_ = 6;
            v___x_2224_ = lean_uint32_shift_left(v___x_2222_, v___x_2223_);
            v___x_2225_ = lean_uint8_to_uint32(v_b_u2081_2221_);
            v_r_2226_ = lean_uint32_lor(v___x_2224_, v___x_2225_);
            v___x_2227_ = 128;
            v___x_2228_ = lean_uint32_dec_lt(v_r_2226_, v___x_2227_);
            return v_r_2226_;
        }
    } else {
        let mut v___x_2229_: u32 = 0;
        v___x_2229_ = lean_uint8_to_uint32(v___x_2127_);
        return v___x_2229_;
    }
}
pub unsafe fn l_ByteArray_utf8DecodeChar___boxed(
    mut v_bytes_2230_: *mut crate::leanh::LeanObject,
    mut v_i_2231_: *mut crate::leanh::LeanObject,
    mut v_h_2232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2233_: u32 = 0;
    let mut v_r_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2233_ = l_ByteArray_utf8DecodeChar(v_bytes_2230_, v_i_2231_, v_h_2232_);
    crate::leanh::lean_dec(v_i_2231_);
    crate::leanh::lean_dec_ref(v_bytes_2230_);
    v_r_2234_ = crate::leanh::lean_box_uint32(v_res_2233_);
    return v_r_2234_;
}
pub unsafe fn l_UInt8_instDecidableIsUTF8FirstByte___aux__1(mut v_c_2235_: u8) -> u8 {
    let mut v___x_2236_: u8 = 0;
    let mut v___x_2237_: u8 = 0;
    let mut v___x_2238_: u8 = 0;
    let mut v___x_2239_: u8 = 0;
    v___x_2236_ = 128;
    v___x_2237_ = lean_uint8_land(v_c_2235_, v___x_2236_);
    v___x_2238_ = 0;
    v___x_2239_ = lean_uint8_dec_eq(v___x_2237_, v___x_2238_);
    if v___x_2239_ == 0 {
        let mut v___x_2240_: u8 = 0;
        let mut v___x_2241_: u8 = 0;
        let mut v___x_2242_: u8 = 0;
        let mut v___x_2243_: u8 = 0;
        v___x_2240_ = 224;
        v___x_2241_ = lean_uint8_land(v_c_2235_, v___x_2240_);
        v___x_2242_ = 192;
        v___x_2243_ = lean_uint8_dec_eq(v___x_2241_, v___x_2242_);
        if v___x_2243_ == 0 {
            let mut v___x_2244_: u8 = 0;
            let mut v___x_2245_: u8 = 0;
            let mut v___x_2246_: u8 = 0;
            v___x_2244_ = 240;
            v___x_2245_ = lean_uint8_land(v_c_2235_, v___x_2244_);
            v___x_2246_ = lean_uint8_dec_eq(v___x_2245_, v___x_2240_);
            if v___x_2246_ == 0 {
                let mut v___x_2247_: u8 = 0;
                let mut v___x_2248_: u8 = 0;
                let mut v___x_2249_: u8 = 0;
                v___x_2247_ = 248;
                v___x_2248_ = lean_uint8_land(v_c_2235_, v___x_2247_);
                v___x_2249_ = lean_uint8_dec_eq(v___x_2248_, v___x_2244_);
                return v___x_2249_;
            } else {
                return v___x_2246_;
            }
        } else {
            return v___x_2243_;
        }
    } else {
        return v___x_2239_;
    }
}
pub unsafe fn l_UInt8_instDecidableIsUTF8FirstByte___aux__1___boxed(
    mut v_c_2250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2251_: u8 = 0;
    let mut v_res_2252_: u8 = 0;
    let mut v_r_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2251_ = (crate::leanh::lean_unbox(v_c_2250_) as u8);
    v_res_2252_ = l_UInt8_instDecidableIsUTF8FirstByte___aux__1(v_c_boxed_2251_);
    v_r_2253_ = crate::leanh::lean_box((v_res_2252_) as usize);
    return v_r_2253_;
}
pub unsafe fn l_UInt8_instDecidableIsUTF8FirstByte(mut v___y_2254_: u8) -> u8 {
    let mut v___x_2255_: u8 = 0;
    v___x_2255_ = l_UInt8_instDecidableIsUTF8FirstByte___aux__1(v___y_2254_);
    return v___x_2255_;
}
pub unsafe fn l_UInt8_instDecidableIsUTF8FirstByte___boxed(
    mut v___y_2256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4__boxed_2257_: u8 = 0;
    let mut v_res_2258_: u8 = 0;
    let mut v_r_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_4__boxed_2257_ = (crate::leanh::lean_unbox(v___y_2256_) as u8);
    v_res_2258_ = l_UInt8_instDecidableIsUTF8FirstByte(v___y_4__boxed_2257_);
    v_r_2259_ = crate::leanh::lean_box((v_res_2258_) as usize);
    return v_r_2259_;
}
pub unsafe fn l_UInt8_utf8ByteSize___redArg(mut v_c_2260_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_2261_: u8 = 0;
    let mut v___x_2262_: u8 = 0;
    let mut v___x_2263_: u8 = 0;
    let mut v___x_2264_: u8 = 0;
    v___x_2261_ = 128;
    v___x_2262_ = lean_uint8_land(v_c_2260_, v___x_2261_);
    v___x_2263_ = 0;
    v___x_2264_ = lean_uint8_dec_eq(v___x_2262_, v___x_2263_);
    if v___x_2264_ == 0 {
        let mut v___x_2265_: u8 = 0;
        let mut v___x_2266_: u8 = 0;
        let mut v___x_2267_: u8 = 0;
        let mut v___x_2268_: u8 = 0;
        v___x_2265_ = 224;
        v___x_2266_ = lean_uint8_land(v_c_2260_, v___x_2265_);
        v___x_2267_ = 192;
        v___x_2268_ = lean_uint8_dec_eq(v___x_2266_, v___x_2267_);
        if v___x_2268_ == 0 {
            let mut v___x_2269_: u8 = 0;
            let mut v___x_2270_: u8 = 0;
            let mut v___x_2271_: u8 = 0;
            v___x_2269_ = 240;
            v___x_2270_ = lean_uint8_land(v_c_2260_, v___x_2269_);
            v___x_2271_ = lean_uint8_dec_eq(v___x_2270_, v___x_2265_);
            if v___x_2271_ == 0 {
                let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2272_ = crate::leanh::lean_unsigned_to_nat(4);
                return v___x_2272_;
            } else {
                let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2273_ = crate::leanh::lean_unsigned_to_nat(3);
                return v___x_2273_;
            }
        } else {
            let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2274_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2274_;
        }
    } else {
        let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2275_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_2275_;
    }
}
pub unsafe fn l_UInt8_utf8ByteSize___redArg___boxed(
    mut v_c_2276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2277_: u8 = 0;
    let mut v_res_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2277_ = (crate::leanh::lean_unbox(v_c_2276_) as u8);
    v_res_2278_ = l_UInt8_utf8ByteSize___redArg(v_c_boxed_2277_);
    return v_res_2278_;
}
pub unsafe fn l_UInt8_utf8ByteSize(
    mut v_c_2279_: u8,
    mut v___h_2280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2281_: u8 = 0;
    let mut v___x_2282_: u8 = 0;
    let mut v___x_2283_: u8 = 0;
    let mut v___x_2284_: u8 = 0;
    v___x_2281_ = 128;
    v___x_2282_ = lean_uint8_land(v_c_2279_, v___x_2281_);
    v___x_2283_ = 0;
    v___x_2284_ = lean_uint8_dec_eq(v___x_2282_, v___x_2283_);
    if v___x_2284_ == 0 {
        let mut v___x_2285_: u8 = 0;
        let mut v___x_2286_: u8 = 0;
        let mut v___x_2287_: u8 = 0;
        let mut v___x_2288_: u8 = 0;
        v___x_2285_ = 224;
        v___x_2286_ = lean_uint8_land(v_c_2279_, v___x_2285_);
        v___x_2287_ = 192;
        v___x_2288_ = lean_uint8_dec_eq(v___x_2286_, v___x_2287_);
        if v___x_2288_ == 0 {
            let mut v___x_2289_: u8 = 0;
            let mut v___x_2290_: u8 = 0;
            let mut v___x_2291_: u8 = 0;
            v___x_2289_ = 240;
            v___x_2290_ = lean_uint8_land(v_c_2279_, v___x_2289_);
            v___x_2291_ = lean_uint8_dec_eq(v___x_2290_, v___x_2285_);
            if v___x_2291_ == 0 {
                let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2292_ = crate::leanh::lean_unsigned_to_nat(4);
                return v___x_2292_;
            } else {
                let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2293_ = crate::leanh::lean_unsigned_to_nat(3);
                return v___x_2293_;
            }
        } else {
            let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2294_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2294_;
        }
    } else {
        let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2295_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_2295_;
    }
}
pub unsafe fn l_UInt8_utf8ByteSize___boxed(
    mut v_c_2296_: *mut crate::leanh::LeanObject,
    mut v___h_2297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2298_: u8 = 0;
    let mut v_res_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2298_ = (crate::leanh::lean_unbox(v_c_2296_) as u8);
    v_res_2299_ = l_UInt8_utf8ByteSize(v_c_boxed_2298_, v___h_2297_);
    return v_res_2299_;
}
pub unsafe fn l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(
    mut v_x_2300_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_2300_ {
        0 => {
            let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2301_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2301_;
        }
        1 => {
            let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2302_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2302_;
        }
        2 => {
            let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2303_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2303_;
        }
        3 => {
            let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2304_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_2304_;
        }
        _ => {
            let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2305_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_2305_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize___boxed(
    mut v_x_2306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_54__boxed_2307_: u8 = 0;
    let mut v_res_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_54__boxed_2307_ = (crate::leanh::lean_unbox(v_x_2306_) as u8);
    v_res_2308_ =
        l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize(
            v_x_54__boxed_2307_,
        );
    return v_res_2308_;
}
pub unsafe fn l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(
    mut v_x_2309_: u8,
    mut v_h__1_2310_: *mut crate::leanh::LeanObject,
    mut v_h__2_2311_: *mut crate::leanh::LeanObject,
    mut v_h__3_2312_: *mut crate::leanh::LeanObject,
    mut v_h__4_2313_: *mut crate::leanh::LeanObject,
    mut v_h__5_2314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_2309_ {
        0 => {
            let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_2314_);
            crate::leanh::lean_dec(v_h__4_2313_);
            crate::leanh::lean_dec(v_h__3_2312_);
            crate::leanh::lean_dec(v_h__2_2311_);
            v___x_2315_ = crate::leanh::lean_box(0);
            v___x_2316_ = crate::leanh::lean_apply_1(v_h__1_2310_, v___x_2315_);
            return v___x_2316_;
        }
        1 => {
            let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_2314_);
            crate::leanh::lean_dec(v_h__4_2313_);
            crate::leanh::lean_dec(v_h__3_2312_);
            crate::leanh::lean_dec(v_h__1_2310_);
            v___x_2317_ = crate::leanh::lean_box(0);
            v___x_2318_ = crate::leanh::lean_apply_1(v_h__2_2311_, v___x_2317_);
            return v___x_2318_;
        }
        2 => {
            let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_2314_);
            crate::leanh::lean_dec(v_h__4_2313_);
            crate::leanh::lean_dec(v_h__2_2311_);
            crate::leanh::lean_dec(v_h__1_2310_);
            v___x_2319_ = crate::leanh::lean_box(0);
            v___x_2320_ = crate::leanh::lean_apply_1(v_h__3_2312_, v___x_2319_);
            return v___x_2320_;
        }
        3 => {
            let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_2314_);
            crate::leanh::lean_dec(v_h__3_2312_);
            crate::leanh::lean_dec(v_h__2_2311_);
            crate::leanh::lean_dec(v_h__1_2310_);
            v___x_2321_ = crate::leanh::lean_box(0);
            v___x_2322_ = crate::leanh::lean_apply_1(v_h__4_2313_, v___x_2321_);
            return v___x_2322_;
        }
        _ => {
            let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_2313_);
            crate::leanh::lean_dec(v_h__3_2312_);
            crate::leanh::lean_dec(v_h__2_2311_);
            crate::leanh::lean_dec(v_h__1_2310_);
            v___x_2323_ = crate::leanh::lean_box(0);
            v___x_2324_ = crate::leanh::lean_apply_1(v_h__5_2314_, v___x_2323_);
            return v___x_2324_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg___boxed(
    mut v_x_2325_: *mut crate::leanh::LeanObject,
    mut v_h__1_2326_: *mut crate::leanh::LeanObject,
    mut v_h__2_2327_: *mut crate::leanh::LeanObject,
    mut v_h__3_2328_: *mut crate::leanh::LeanObject,
    mut v_h__4_2329_: *mut crate::leanh::LeanObject,
    mut v_h__5_2330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_56__boxed_2331_: u8 = 0;
    let mut v_res_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_56__boxed_2331_ = (crate::leanh::lean_unbox(v_x_2325_) as u8);
    v_res_2332_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___redArg(v_x_56__boxed_2331_, v_h__1_2326_, v_h__2_2327_, v_h__3_2328_, v_h__4_2329_, v_h__5_2330_);
    return v_res_2332_;
}
pub unsafe fn l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(
    mut v_motive_2333_: *mut crate::leanh::LeanObject,
    mut v_x_2334_: u8,
    mut v_h__1_2335_: *mut crate::leanh::LeanObject,
    mut v_h__2_2336_: *mut crate::leanh::LeanObject,
    mut v_h__3_2337_: *mut crate::leanh::LeanObject,
    mut v_h__4_2338_: *mut crate::leanh::LeanObject,
    mut v_h__5_2339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_2334_ {
        0 => {
            let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_2339_);
            crate::leanh::lean_dec(v_h__4_2338_);
            crate::leanh::lean_dec(v_h__3_2337_);
            crate::leanh::lean_dec(v_h__2_2336_);
            v___x_2340_ = crate::leanh::lean_box(0);
            v___x_2341_ = crate::leanh::lean_apply_1(v_h__1_2335_, v___x_2340_);
            return v___x_2341_;
        }
        1 => {
            let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_2339_);
            crate::leanh::lean_dec(v_h__4_2338_);
            crate::leanh::lean_dec(v_h__3_2337_);
            crate::leanh::lean_dec(v_h__1_2335_);
            v___x_2342_ = crate::leanh::lean_box(0);
            v___x_2343_ = crate::leanh::lean_apply_1(v_h__2_2336_, v___x_2342_);
            return v___x_2343_;
        }
        2 => {
            let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_2339_);
            crate::leanh::lean_dec(v_h__4_2338_);
            crate::leanh::lean_dec(v_h__2_2336_);
            crate::leanh::lean_dec(v_h__1_2335_);
            v___x_2344_ = crate::leanh::lean_box(0);
            v___x_2345_ = crate::leanh::lean_apply_1(v_h__3_2337_, v___x_2344_);
            return v___x_2345_;
        }
        3 => {
            let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_2339_);
            crate::leanh::lean_dec(v_h__3_2337_);
            crate::leanh::lean_dec(v_h__2_2336_);
            crate::leanh::lean_dec(v_h__1_2335_);
            v___x_2346_ = crate::leanh::lean_box(0);
            v___x_2347_ = crate::leanh::lean_apply_1(v_h__4_2338_, v___x_2346_);
            return v___x_2347_;
        }
        _ => {
            let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_2338_);
            crate::leanh::lean_dec(v_h__3_2337_);
            crate::leanh::lean_dec(v_h__2_2336_);
            crate::leanh::lean_dec(v_h__1_2335_);
            v___x_2348_ = crate::leanh::lean_box(0);
            v___x_2349_ = crate::leanh::lean_apply_1(v_h__5_2339_, v___x_2348_);
            return v___x_2349_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter___boxed(
    mut v_motive_2350_: *mut crate::leanh::LeanObject,
    mut v_x_2351_: *mut crate::leanh::LeanObject,
    mut v_h__1_2352_: *mut crate::leanh::LeanObject,
    mut v_h__2_2353_: *mut crate::leanh::LeanObject,
    mut v_h__3_2354_: *mut crate::leanh::LeanObject,
    mut v_h__4_2355_: *mut crate::leanh::LeanObject,
    mut v_h__5_2356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_79__boxed_2357_: u8 = 0;
    let mut v_res_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_79__boxed_2357_ = (crate::leanh::lean_unbox(v_x_2351_) as u8);
    v_res_2358_ = l___private_Init_Data_String_Decode_0__ByteArray_utf8DecodeChar_x3f_FirstByte_utf8ByteSize_match__1_splitter(v_motive_2350_, v_x_79__boxed_2357_, v_h__1_2352_, v_h__2_2353_, v_h__3_2354_, v_h__4_2355_, v_h__5_2356_);
    return v_res_2358_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Decode(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Char_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Bitwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
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
pub unsafe fn meta_initialize_Init_Data_String_Decode(
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
pub unsafe fn initialize_Init_Data_String_Decode(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Char_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ByteArray_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ByteArray_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_MinMax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Bitwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Decode(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Decode(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Decode(builtin);
}
