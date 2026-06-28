// Lean compiler output
// Module: Lean.Compiler.IR.LLVMBindings
// Imports: Init.System.IO
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
use crate::lean_imports_rs::Init::Prelude::lean_usize_dec_eq;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_box_uint64, lean_box_usize, lean_dec,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_unbox, lean_unbox_uint64,
    lean_unbox_usize,
};
pub static mut l_LLVM_CodegenFileType_AssemblyFile: u64 = 0;
pub static mut l_LLVM_CodegenFileType_ObjectFile: u64 = 0;
pub static mut l_LLVM_IntPredicate_EQ: u64 = 0;
pub static mut l_LLVM_IntPredicate_NE: u64 = 0;
pub static mut l_LLVM_IntPredicate_UGT: u64 = 0;
pub static mut l_LLVM_AttributeIndex_AttributeReturnIndex: u64 = 0;
pub static mut l_LLVM_AttributeIndex_AttributeFunctionIndex: u64 = 0;
pub static mut l_LLVM_Visibility_default: u64 = 0;
pub static mut l_LLVM_Visibility_hidden: u64 = 0;
pub static mut l_LLVM_Visibility_protected: u64 = 0;
pub static mut l_LLVM_DLLStorageClass_default: u64 = 0;
pub static mut l_LLVM_DLLStorageClass_import: u64 = 0;
pub static mut l_LLVM_DLLStorageClass_export: u64 = 0;
pub static mut l_LLVM_Linkage_external: u64 = 0;
pub static mut l_LLVM_Linkage_availableExternally: u64 = 0;
pub static mut l_LLVM_Linkage_linkOnceAny: u64 = 0;
pub static mut l_LLVM_Linkage_linkOnceODR: u64 = 0;
pub static mut l_LLVM_Linkage_linkOnceODRAutoHide: u64 = 0;
pub static mut l_LLVM_Linkage_weakAny: u64 = 0;
pub static mut l_LLVM_Linkage_weakODR: u64 = 0;
pub static mut l_LLVM_Linkage_appending: u64 = 0;
pub static mut l_LLVM_Linkage_internal: u64 = 0;
pub static mut l_LLVM_Linkage_private: u64 = 0;
pub static mut l_LLVM_Linkage_dllImport: u64 = 0;
pub static mut l_LLVM_Linkage_dllExport: u64 = 0;
pub static mut l_LLVM_Linkage_externalWeak: u64 = 0;
pub static mut l_LLVM_Linkage_ghost: u64 = 0;
pub static mut l_LLVM_Linkage_common: u64 = 0;
pub static mut l_LLVM_Linkage_linkerPrivate: u64 = 0;
pub static mut l_LLVM_Linkage_linkerPrivateWeak: u64 = 0;
pub unsafe fn _init_l_LLVM_CodegenFileType_AssemblyFile() -> u64 {
    let mut v___x_1242_: u64 = 0;
    v___x_1242_ = 0u64;
    return v___x_1242_;
}
pub unsafe fn _init_l_LLVM_CodegenFileType_ObjectFile() -> u64 {
    let mut v___x_1243_: u64 = 0;
    v___x_1243_ = 1u64;
    return v___x_1243_;
}
pub unsafe fn _init_l_LLVM_IntPredicate_EQ() -> u64 {
    let mut v___x_1244_: u64 = 0;
    v___x_1244_ = 32u64;
    return v___x_1244_;
}
pub unsafe fn _init_l_LLVM_IntPredicate_NE() -> u64 {
    let mut v___x_1245_: u64 = 0;
    v___x_1245_ = 33u64;
    return v___x_1245_;
}
pub unsafe fn _init_l_LLVM_IntPredicate_UGT() -> u64 {
    let mut v___x_1246_: u64 = 0;
    v___x_1246_ = 34u64;
    return v___x_1246_;
}
pub unsafe fn _init_l_LLVM_AttributeIndex_AttributeReturnIndex() -> u64 {
    let mut v___x_1247_: u64 = 0;
    v___x_1247_ = 0u64;
    return v___x_1247_;
}
pub unsafe fn _init_l_LLVM_AttributeIndex_AttributeFunctionIndex() -> u64 {
    let mut v___x_1248_: u64 = 0;
    v___x_1248_ = 18446744073709551615u64;
    return v___x_1248_;
}
pub unsafe fn l_LLVM_Value_isNull___redArg(mut v_v_1249_: usize) -> u8 {
    let mut v___x_1250_: usize = 0;
    let mut v___x_1251_: u8 = 0;
    v___x_1250_ = 0usize;
    v___x_1251_ = lean_usize_dec_eq(v_v_1249_, v___x_1250_);
    return v___x_1251_;
}
pub unsafe fn l_LLVM_Value_isNull___redArg___boxed(
    mut v_v_1252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_1253_: usize = 0;
    let mut v_res_1254_: u8 = 0;
    let mut v_r_1255_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_1253_ = lean_unbox_usize(v_v_1252_);
    lean_dec(v_v_1252_);
    v_res_1254_ = l_LLVM_Value_isNull___redArg(v_v_boxed_1253_);
    v_r_1255_ = lean_box((v_res_1254_) as usize);
    return v_r_1255_;
}
pub unsafe fn l_LLVM_Value_isNull(mut v_ctx_1256_: usize, mut v_v_1257_: usize) -> u8 {
    let mut v___x_1258_: u8 = 0;
    v___x_1258_ = l_LLVM_Value_isNull___redArg(v_v_1257_);
    return v___x_1258_;
}
pub unsafe fn l_LLVM_Value_isNull___boxed(
    mut v_ctx_1259_: *mut LeanObject,
    mut v_v_1260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1261_: usize = 0;
    let mut v_v_boxed_1262_: usize = 0;
    let mut v_res_1263_: u8 = 0;
    let mut v_r_1264_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1261_ = lean_unbox_usize(v_ctx_1259_);
    lean_dec(v_ctx_1259_);
    v_v_boxed_1262_ = lean_unbox_usize(v_v_1260_);
    lean_dec(v_v_1260_);
    v_res_1263_ = l_LLVM_Value_isNull(v_ctx_boxed_1261_, v_v_boxed_1262_);
    v_r_1264_ = lean_box((v_res_1263_) as usize);
    return v_r_1264_;
}
pub unsafe fn l_LLVM_Value_getName___boxed(
    mut v_ctx_1268_: *mut LeanObject,
    mut v_value_1269_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1271_: usize = 0;
    let mut v_value_boxed_1272_: usize = 0;
    let mut v_res_1273_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1271_ = lean_unbox_usize(v_ctx_1268_);
    lean_dec(v_ctx_1268_);
    v_value_boxed_1272_ = lean_unbox_usize(v_value_1269_);
    lean_dec(v_value_1269_);
    v_res_1273_ = lean_llvm_get_value_name2(v_ctx_boxed_1271_, v_value_boxed_1272_);
    return v_res_1273_;
}
pub unsafe fn l_LLVM_llvmInitializeTargetInfo___boxed(
    mut v_a_00___x40___internal___hyg_1275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1276_: *mut LeanObject = core::ptr::null_mut();
    v_res_1276_ = lean_llvm_initialize_target_info();
    return v_res_1276_;
}
pub unsafe fn l_LLVM_createContext___boxed(
    mut v_a_00___x40___internal___hyg_1278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1279_: usize = 0;
    let mut v_r_1280_: *mut LeanObject = core::ptr::null_mut();
    v_res_1279_ = lean_llvm_create_context();
    v_r_1280_ = lean_box_usize(v_res_1279_);
    return v_r_1280_;
}
pub unsafe fn l_LLVM_createModule___boxed(
    mut v_ctx_1284_: *mut LeanObject,
    mut v_name_1285_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1287_: usize = 0;
    let mut v_res_1288_: usize = 0;
    let mut v_r_1289_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1287_ = lean_unbox_usize(v_ctx_1284_);
    lean_dec(v_ctx_1284_);
    v_res_1288_ = lean_llvm_create_module(v_ctx_boxed_1287_, v_name_1285_);
    lean_dec_ref(v_name_1285_);
    v_r_1289_ = lean_box_usize(v_res_1288_);
    return v_r_1289_;
}
pub unsafe fn l_LLVM_moduleToString___boxed(
    mut v_ctx_1293_: *mut LeanObject,
    mut v_m_1294_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1296_: usize = 0;
    let mut v_m_boxed_1297_: usize = 0;
    let mut v_res_1298_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1296_ = lean_unbox_usize(v_ctx_1293_);
    lean_dec(v_ctx_1293_);
    v_m_boxed_1297_ = lean_unbox_usize(v_m_1294_);
    lean_dec(v_m_1294_);
    v_res_1298_ = lean_llvm_module_to_string(v_ctx_boxed_1296_, v_m_boxed_1297_);
    return v_res_1298_;
}
pub unsafe fn l_LLVM_writeBitcodeToFile___boxed(
    mut v_ctx_1303_: *mut LeanObject,
    mut v_m_1304_: *mut LeanObject,
    mut v_path_1305_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1307_: usize = 0;
    let mut v_m_boxed_1308_: usize = 0;
    let mut v_res_1309_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1307_ = lean_unbox_usize(v_ctx_1303_);
    lean_dec(v_ctx_1303_);
    v_m_boxed_1308_ = lean_unbox_usize(v_m_1304_);
    lean_dec(v_m_1304_);
    v_res_1309_ = lean_llvm_write_bitcode_to_file(v_ctx_boxed_1307_, v_m_boxed_1308_, v_path_1305_);
    lean_dec_ref(v_path_1305_);
    return v_res_1309_;
}
pub unsafe fn l_LLVM_addFunction___boxed(
    mut v_ctx_1315_: *mut LeanObject,
    mut v_m_1316_: *mut LeanObject,
    mut v_name_1317_: *mut LeanObject,
    mut v_type_1318_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1320_: usize = 0;
    let mut v_m_boxed_1321_: usize = 0;
    let mut v_type_boxed_1322_: usize = 0;
    let mut v_res_1323_: usize = 0;
    let mut v_r_1324_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1320_ = lean_unbox_usize(v_ctx_1315_);
    lean_dec(v_ctx_1315_);
    v_m_boxed_1321_ = lean_unbox_usize(v_m_1316_);
    lean_dec(v_m_1316_);
    v_type_boxed_1322_ = lean_unbox_usize(v_type_1318_);
    lean_dec(v_type_1318_);
    v_res_1323_ = lean_llvm_add_function(
        v_ctx_boxed_1320_,
        v_m_boxed_1321_,
        v_name_1317_,
        v_type_boxed_1322_,
    );
    lean_dec_ref(v_name_1317_);
    v_r_1324_ = lean_box_usize(v_res_1323_);
    return v_r_1324_;
}
pub unsafe fn l_LLVM_getFirstFunction___boxed(
    mut v_ctx_1328_: *mut LeanObject,
    mut v_m_1329_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1331_: usize = 0;
    let mut v_m_boxed_1332_: usize = 0;
    let mut v_res_1333_: usize = 0;
    let mut v_r_1334_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1331_ = lean_unbox_usize(v_ctx_1328_);
    lean_dec(v_ctx_1328_);
    v_m_boxed_1332_ = lean_unbox_usize(v_m_1329_);
    lean_dec(v_m_1329_);
    v_res_1333_ = lean_llvm_get_first_function(v_ctx_boxed_1331_, v_m_boxed_1332_);
    v_r_1334_ = lean_box_usize(v_res_1333_);
    return v_r_1334_;
}
pub unsafe fn l_LLVM_getNextFunction___boxed(
    mut v_ctx_1338_: *mut LeanObject,
    mut v_glbl_1339_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1341_: usize = 0;
    let mut v_glbl_boxed_1342_: usize = 0;
    let mut v_res_1343_: usize = 0;
    let mut v_r_1344_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1341_ = lean_unbox_usize(v_ctx_1338_);
    lean_dec(v_ctx_1338_);
    v_glbl_boxed_1342_ = lean_unbox_usize(v_glbl_1339_);
    lean_dec(v_glbl_1339_);
    v_res_1343_ = lean_llvm_get_next_function(v_ctx_boxed_1341_, v_glbl_boxed_1342_);
    v_r_1344_ = lean_box_usize(v_res_1343_);
    return v_r_1344_;
}
pub unsafe fn l_LLVM_getNamedFunction___boxed(
    mut v_ctx_1349_: *mut LeanObject,
    mut v_m_1350_: *mut LeanObject,
    mut v_name_1351_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1353_: usize = 0;
    let mut v_m_boxed_1354_: usize = 0;
    let mut v_res_1355_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1353_ = lean_unbox_usize(v_ctx_1349_);
    lean_dec(v_ctx_1349_);
    v_m_boxed_1354_ = lean_unbox_usize(v_m_1350_);
    lean_dec(v_m_1350_);
    v_res_1355_ = lean_llvm_get_named_function(v_ctx_boxed_1353_, v_m_boxed_1354_, v_name_1351_);
    lean_dec_ref(v_name_1351_);
    return v_res_1355_;
}
pub unsafe fn l_LLVM_addGlobal___boxed(
    mut v_ctx_1361_: *mut LeanObject,
    mut v_m_1362_: *mut LeanObject,
    mut v_name_1363_: *mut LeanObject,
    mut v_type_1364_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1366_: usize = 0;
    let mut v_m_boxed_1367_: usize = 0;
    let mut v_type_boxed_1368_: usize = 0;
    let mut v_res_1369_: usize = 0;
    let mut v_r_1370_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1366_ = lean_unbox_usize(v_ctx_1361_);
    lean_dec(v_ctx_1361_);
    v_m_boxed_1367_ = lean_unbox_usize(v_m_1362_);
    lean_dec(v_m_1362_);
    v_type_boxed_1368_ = lean_unbox_usize(v_type_1364_);
    lean_dec(v_type_1364_);
    v_res_1369_ = lean_llvm_add_global(
        v_ctx_boxed_1366_,
        v_m_boxed_1367_,
        v_name_1363_,
        v_type_boxed_1368_,
    );
    lean_dec_ref(v_name_1363_);
    v_r_1370_ = lean_box_usize(v_res_1369_);
    return v_r_1370_;
}
pub unsafe fn l_LLVM_getNamedGlobal___boxed(
    mut v_ctx_1375_: *mut LeanObject,
    mut v_m_1376_: *mut LeanObject,
    mut v_name_1377_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1379_: usize = 0;
    let mut v_m_boxed_1380_: usize = 0;
    let mut v_res_1381_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1379_ = lean_unbox_usize(v_ctx_1375_);
    lean_dec(v_ctx_1375_);
    v_m_boxed_1380_ = lean_unbox_usize(v_m_1376_);
    lean_dec(v_m_1376_);
    v_res_1381_ = lean_llvm_get_named_global(v_ctx_boxed_1379_, v_m_boxed_1380_, v_name_1377_);
    lean_dec_ref(v_name_1377_);
    return v_res_1381_;
}
pub unsafe fn l_LLVM_getFirstGlobal___boxed(
    mut v_ctx_1385_: *mut LeanObject,
    mut v_m_1386_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1388_: usize = 0;
    let mut v_m_boxed_1389_: usize = 0;
    let mut v_res_1390_: usize = 0;
    let mut v_r_1391_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1388_ = lean_unbox_usize(v_ctx_1385_);
    lean_dec(v_ctx_1385_);
    v_m_boxed_1389_ = lean_unbox_usize(v_m_1386_);
    lean_dec(v_m_1386_);
    v_res_1390_ = lean_llvm_get_first_global(v_ctx_boxed_1388_, v_m_boxed_1389_);
    v_r_1391_ = lean_box_usize(v_res_1390_);
    return v_r_1391_;
}
pub unsafe fn l_LLVM_getNextGlobal___boxed(
    mut v_ctx_1395_: *mut LeanObject,
    mut v_glbl_1396_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1398_: usize = 0;
    let mut v_glbl_boxed_1399_: usize = 0;
    let mut v_res_1400_: usize = 0;
    let mut v_r_1401_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1398_ = lean_unbox_usize(v_ctx_1395_);
    lean_dec(v_ctx_1395_);
    v_glbl_boxed_1399_ = lean_unbox_usize(v_glbl_1396_);
    lean_dec(v_glbl_1396_);
    v_res_1400_ = lean_llvm_get_next_global(v_ctx_boxed_1398_, v_glbl_boxed_1399_);
    v_r_1401_ = lean_box_usize(v_res_1400_);
    return v_r_1401_;
}
pub unsafe fn l_LLVM_buildGlobalString___boxed(
    mut v_ctx_1407_: *mut LeanObject,
    mut v_builder_1408_: *mut LeanObject,
    mut v_value_1409_: *mut LeanObject,
    mut v_name_1410_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1412_: usize = 0;
    let mut v_builder_boxed_1413_: usize = 0;
    let mut v_res_1414_: usize = 0;
    let mut v_r_1415_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1412_ = lean_unbox_usize(v_ctx_1407_);
    lean_dec(v_ctx_1407_);
    v_builder_boxed_1413_ = lean_unbox_usize(v_builder_1408_);
    lean_dec(v_builder_1408_);
    v_res_1414_ = lean_llvm_build_global_string(
        v_ctx_boxed_1412_,
        v_builder_boxed_1413_,
        v_value_1409_,
        v_name_1410_,
    );
    lean_dec_ref(v_value_1409_);
    v_r_1415_ = lean_box_usize(v_res_1414_);
    return v_r_1415_;
}
pub unsafe fn l_LLVM_isDeclaration___boxed(
    mut v_ctx_1419_: *mut LeanObject,
    mut v_global_1420_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1422_: usize = 0;
    let mut v_global_boxed_1423_: usize = 0;
    let mut v_res_1424_: u8 = 0;
    let mut v_r_1425_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1422_ = lean_unbox_usize(v_ctx_1419_);
    lean_dec(v_ctx_1419_);
    v_global_boxed_1423_ = lean_unbox_usize(v_global_1420_);
    lean_dec(v_global_1420_);
    v_res_1424_ = llvm_is_declaration(v_ctx_boxed_1422_, v_global_boxed_1423_);
    v_r_1425_ = lean_box((v_res_1424_) as usize);
    return v_r_1425_;
}
pub unsafe fn l_LLVM_setInitializer___boxed(
    mut v_ctx_1430_: *mut LeanObject,
    mut v_glbl_1431_: *mut LeanObject,
    mut v_val_1432_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1434_: usize = 0;
    let mut v_glbl_boxed_1435_: usize = 0;
    let mut v_val_boxed_1436_: usize = 0;
    let mut v_res_1437_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1434_ = lean_unbox_usize(v_ctx_1430_);
    lean_dec(v_ctx_1430_);
    v_glbl_boxed_1435_ = lean_unbox_usize(v_glbl_1431_);
    lean_dec(v_glbl_1431_);
    v_val_boxed_1436_ = lean_unbox_usize(v_val_1432_);
    lean_dec(v_val_1432_);
    v_res_1437_ =
        lean_llvm_set_initializer(v_ctx_boxed_1434_, v_glbl_boxed_1435_, v_val_boxed_1436_);
    return v_res_1437_;
}
pub unsafe fn l_LLVM_functionType___boxed(
    mut v_ctx_1443_: *mut LeanObject,
    mut v_retty_1444_: *mut LeanObject,
    mut v_args_1445_: *mut LeanObject,
    mut v_isVarArg_1446_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1448_: usize = 0;
    let mut v_retty_boxed_1449_: usize = 0;
    let mut v_isVarArg_boxed_1450_: u8 = 0;
    let mut v_res_1451_: usize = 0;
    let mut v_r_1452_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1448_ = lean_unbox_usize(v_ctx_1443_);
    lean_dec(v_ctx_1443_);
    v_retty_boxed_1449_ = lean_unbox_usize(v_retty_1444_);
    lean_dec(v_retty_1444_);
    v_isVarArg_boxed_1450_ = (lean_unbox(v_isVarArg_1446_) as u8);
    v_res_1451_ = lean_llvm_function_type(
        v_ctx_boxed_1448_,
        v_retty_boxed_1449_,
        v_args_1445_,
        v_isVarArg_boxed_1450_,
    );
    lean_dec_ref(v_args_1445_);
    v_r_1452_ = lean_box_usize(v_res_1451_);
    return v_r_1452_;
}
pub unsafe fn l_LLVM_voidType___boxed(
    mut v_ctx_1455_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1457_: usize = 0;
    let mut v_res_1458_: usize = 0;
    let mut v_r_1459_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1457_ = lean_unbox_usize(v_ctx_1455_);
    lean_dec(v_ctx_1455_);
    v_res_1458_ = lean_llvm_void_type_in_context(v_ctx_boxed_1457_);
    v_r_1459_ = lean_box_usize(v_res_1458_);
    return v_r_1459_;
}
pub unsafe fn l_LLVM_intTypeInContext___boxed(
    mut v_ctx_1463_: *mut LeanObject,
    mut v_width_1464_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1466_: usize = 0;
    let mut v_width_boxed_1467_: u64 = 0;
    let mut v_res_1468_: usize = 0;
    let mut v_r_1469_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1466_ = lean_unbox_usize(v_ctx_1463_);
    lean_dec(v_ctx_1463_);
    v_width_boxed_1467_ = lean_unbox_uint64(v_width_1464_);
    lean_dec_ref(v_width_1464_);
    v_res_1468_ = lean_llvm_int_type_in_context(v_ctx_boxed_1466_, v_width_boxed_1467_);
    v_r_1469_ = lean_box_usize(v_res_1468_);
    return v_r_1469_;
}
pub unsafe fn l_LLVM_opaquePointerTypeInContext___boxed(
    mut v_ctx_1473_: *mut LeanObject,
    mut v_addrspace_1474_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1476_: usize = 0;
    let mut v_addrspace_boxed_1477_: u64 = 0;
    let mut v_res_1478_: usize = 0;
    let mut v_r_1479_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1476_ = lean_unbox_usize(v_ctx_1473_);
    lean_dec(v_ctx_1473_);
    v_addrspace_boxed_1477_ = lean_unbox_uint64(v_addrspace_1474_);
    lean_dec_ref(v_addrspace_1474_);
    v_res_1478_ =
        lean_llvm_opaque_pointer_type_in_context(v_ctx_boxed_1476_, v_addrspace_boxed_1477_);
    v_r_1479_ = lean_box_usize(v_res_1478_);
    return v_r_1479_;
}
pub unsafe fn l_LLVM_floatTypeInContext___boxed(
    mut v_ctx_1482_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1484_: usize = 0;
    let mut v_res_1485_: usize = 0;
    let mut v_r_1486_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1484_ = lean_unbox_usize(v_ctx_1482_);
    lean_dec(v_ctx_1482_);
    v_res_1485_ = lean_llvm_float_type_in_context(v_ctx_boxed_1484_);
    v_r_1486_ = lean_box_usize(v_res_1485_);
    return v_r_1486_;
}
pub unsafe fn l_LLVM_doubleTypeInContext___boxed(
    mut v_ctx_1489_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1491_: usize = 0;
    let mut v_res_1492_: usize = 0;
    let mut v_r_1493_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1491_ = lean_unbox_usize(v_ctx_1489_);
    lean_dec(v_ctx_1489_);
    v_res_1492_ = lean_llvm_double_type_in_context(v_ctx_boxed_1491_);
    v_r_1493_ = lean_box_usize(v_res_1492_);
    return v_r_1493_;
}
pub unsafe fn l_LLVM_pointerType___boxed(
    mut v_ctx_1497_: *mut LeanObject,
    mut v_elemty_1498_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1500_: usize = 0;
    let mut v_elemty_boxed_1501_: usize = 0;
    let mut v_res_1502_: usize = 0;
    let mut v_r_1503_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1500_ = lean_unbox_usize(v_ctx_1497_);
    lean_dec(v_ctx_1497_);
    v_elemty_boxed_1501_ = lean_unbox_usize(v_elemty_1498_);
    lean_dec(v_elemty_1498_);
    v_res_1502_ = lean_llvm_pointer_type(v_ctx_boxed_1500_, v_elemty_boxed_1501_);
    v_r_1503_ = lean_box_usize(v_res_1502_);
    return v_r_1503_;
}
pub unsafe fn l_LLVM_arrayType___boxed(
    mut v_ctx_1508_: *mut LeanObject,
    mut v_elemty_1509_: *mut LeanObject,
    mut v_nelem_1510_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1512_: usize = 0;
    let mut v_elemty_boxed_1513_: usize = 0;
    let mut v_nelem_boxed_1514_: u64 = 0;
    let mut v_res_1515_: usize = 0;
    let mut v_r_1516_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1512_ = lean_unbox_usize(v_ctx_1508_);
    lean_dec(v_ctx_1508_);
    v_elemty_boxed_1513_ = lean_unbox_usize(v_elemty_1509_);
    lean_dec(v_elemty_1509_);
    v_nelem_boxed_1514_ = lean_unbox_uint64(v_nelem_1510_);
    lean_dec_ref(v_nelem_1510_);
    v_res_1515_ =
        lean_llvm_array_type(v_ctx_boxed_1512_, v_elemty_boxed_1513_, v_nelem_boxed_1514_);
    v_r_1516_ = lean_box_usize(v_res_1515_);
    return v_r_1516_;
}
pub unsafe fn l_LLVM_constArray___boxed(
    mut v_ctx_1521_: *mut LeanObject,
    mut v_elemty_1522_: *mut LeanObject,
    mut v_vals_1523_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1525_: usize = 0;
    let mut v_elemty_boxed_1526_: usize = 0;
    let mut v_res_1527_: usize = 0;
    let mut v_r_1528_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1525_ = lean_unbox_usize(v_ctx_1521_);
    lean_dec(v_ctx_1521_);
    v_elemty_boxed_1526_ = lean_unbox_usize(v_elemty_1522_);
    lean_dec(v_elemty_1522_);
    v_res_1527_ = lean_llvm_const_array(v_ctx_boxed_1525_, v_elemty_boxed_1526_, v_vals_1523_);
    lean_dec_ref(v_vals_1523_);
    v_r_1528_ = lean_box_usize(v_res_1527_);
    return v_r_1528_;
}
pub unsafe fn l_LLVM_constString___boxed(
    mut v_ctx_1532_: *mut LeanObject,
    mut v_str_1533_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1535_: usize = 0;
    let mut v_res_1536_: usize = 0;
    let mut v_r_1537_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1535_ = lean_unbox_usize(v_ctx_1532_);
    lean_dec(v_ctx_1532_);
    v_res_1536_ = lean_llvm_const_string(v_ctx_boxed_1535_, v_str_1533_);
    lean_dec_ref(v_str_1533_);
    v_r_1537_ = lean_box_usize(v_res_1536_);
    return v_r_1537_;
}
pub unsafe fn l_LLVM_constPointerNull___boxed(
    mut v_ctx_1541_: *mut LeanObject,
    mut v_elemty_1542_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1544_: usize = 0;
    let mut v_elemty_boxed_1545_: usize = 0;
    let mut v_res_1546_: usize = 0;
    let mut v_r_1547_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1544_ = lean_unbox_usize(v_ctx_1541_);
    lean_dec(v_ctx_1541_);
    v_elemty_boxed_1545_ = lean_unbox_usize(v_elemty_1542_);
    lean_dec(v_elemty_1542_);
    v_res_1546_ = lean_llvm_const_pointer_null(v_ctx_boxed_1544_, v_elemty_boxed_1545_);
    v_r_1547_ = lean_box_usize(v_res_1546_);
    return v_r_1547_;
}
pub unsafe fn l_LLVM_getUndef___boxed(
    mut v_ctx_1551_: *mut LeanObject,
    mut v_elemty_1552_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1554_: usize = 0;
    let mut v_elemty_boxed_1555_: usize = 0;
    let mut v_res_1556_: usize = 0;
    let mut v_r_1557_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1554_ = lean_unbox_usize(v_ctx_1551_);
    lean_dec(v_ctx_1551_);
    v_elemty_boxed_1555_ = lean_unbox_usize(v_elemty_1552_);
    lean_dec(v_elemty_1552_);
    v_res_1556_ = lean_llvm_get_undef(v_ctx_boxed_1554_, v_elemty_boxed_1555_);
    v_r_1557_ = lean_box_usize(v_res_1556_);
    return v_r_1557_;
}
pub unsafe fn l_LLVM_createBuilderInContext___boxed(
    mut v_ctx_1560_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1562_: usize = 0;
    let mut v_res_1563_: usize = 0;
    let mut v_r_1564_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1562_ = lean_unbox_usize(v_ctx_1560_);
    lean_dec(v_ctx_1560_);
    v_res_1563_ = lean_llvm_create_builder_in_context(v_ctx_boxed_1562_);
    v_r_1564_ = lean_box_usize(v_res_1563_);
    return v_r_1564_;
}
pub unsafe fn l_LLVM_appendBasicBlockInContext___boxed(
    mut v_ctx_1569_: *mut LeanObject,
    mut v_fn_1570_: *mut LeanObject,
    mut v_name_1571_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1573_: usize = 0;
    let mut v_fn_boxed_1574_: usize = 0;
    let mut v_res_1575_: usize = 0;
    let mut v_r_1576_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1573_ = lean_unbox_usize(v_ctx_1569_);
    lean_dec(v_ctx_1569_);
    v_fn_boxed_1574_ = lean_unbox_usize(v_fn_1570_);
    lean_dec(v_fn_1570_);
    v_res_1575_ =
        lean_llvm_append_basic_block_in_context(v_ctx_boxed_1573_, v_fn_boxed_1574_, v_name_1571_);
    lean_dec_ref(v_name_1571_);
    v_r_1576_ = lean_box_usize(v_res_1575_);
    return v_r_1576_;
}
pub unsafe fn l_LLVM_countBasicBlocks___boxed(
    mut v_ctx_1580_: *mut LeanObject,
    mut v_fn_1581_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1583_: usize = 0;
    let mut v_fn_boxed_1584_: usize = 0;
    let mut v_res_1585_: u64 = 0;
    let mut v_r_1586_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1583_ = lean_unbox_usize(v_ctx_1580_);
    lean_dec(v_ctx_1580_);
    v_fn_boxed_1584_ = lean_unbox_usize(v_fn_1581_);
    lean_dec(v_fn_1581_);
    v_res_1585_ = lean_llvm_count_basic_blocks(v_ctx_boxed_1583_, v_fn_boxed_1584_);
    v_r_1586_ = lean_box_uint64(v_res_1585_);
    return v_r_1586_;
}
pub unsafe fn l_LLVM_getEntryBasicBlock___boxed(
    mut v_ctx_1590_: *mut LeanObject,
    mut v_fn_1591_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1593_: usize = 0;
    let mut v_fn_boxed_1594_: usize = 0;
    let mut v_res_1595_: usize = 0;
    let mut v_r_1596_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1593_ = lean_unbox_usize(v_ctx_1590_);
    lean_dec(v_ctx_1590_);
    v_fn_boxed_1594_ = lean_unbox_usize(v_fn_1591_);
    lean_dec(v_fn_1591_);
    v_res_1595_ = lean_llvm_get_entry_basic_block(v_ctx_boxed_1593_, v_fn_boxed_1594_);
    v_r_1596_ = lean_box_usize(v_res_1595_);
    return v_r_1596_;
}
pub unsafe fn l_LLVM_getFirstInstruction___boxed(
    mut v_ctx_1600_: *mut LeanObject,
    mut v_bb_1601_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1603_: usize = 0;
    let mut v_bb_boxed_1604_: usize = 0;
    let mut v_res_1605_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1603_ = lean_unbox_usize(v_ctx_1600_);
    lean_dec(v_ctx_1600_);
    v_bb_boxed_1604_ = lean_unbox_usize(v_bb_1601_);
    lean_dec(v_bb_1601_);
    v_res_1605_ = lean_llvm_get_first_instruction(v_ctx_boxed_1603_, v_bb_boxed_1604_);
    return v_res_1605_;
}
pub unsafe fn l_LLVM_positionBuilderBefore___boxed(
    mut v_ctx_1610_: *mut LeanObject,
    mut v_builder_1611_: *mut LeanObject,
    mut v_instr_1612_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1614_: usize = 0;
    let mut v_builder_boxed_1615_: usize = 0;
    let mut v_instr_boxed_1616_: usize = 0;
    let mut v_res_1617_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1614_ = lean_unbox_usize(v_ctx_1610_);
    lean_dec(v_ctx_1610_);
    v_builder_boxed_1615_ = lean_unbox_usize(v_builder_1611_);
    lean_dec(v_builder_1611_);
    v_instr_boxed_1616_ = lean_unbox_usize(v_instr_1612_);
    lean_dec(v_instr_1612_);
    v_res_1617_ = lean_llvm_position_builder_before(
        v_ctx_boxed_1614_,
        v_builder_boxed_1615_,
        v_instr_boxed_1616_,
    );
    return v_res_1617_;
}
pub unsafe fn l_LLVM_positionBuilderAtEnd___boxed(
    mut v_Context_00___x40_Lean_Compiler_IR_LLVMBindings_2945912803____hygCtx___hyg_1623_: *mut LeanObject,
    mut v_ctx_1624_: *mut LeanObject,
    mut v_builder_1625_: *mut LeanObject,
    mut v_bb_1626_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_builder_boxed_1628_: usize = 0;
    let mut v_bb_boxed_1629_: usize = 0;
    let mut v_res_1630_: *mut LeanObject = core::ptr::null_mut();
    v_builder_boxed_1628_ = lean_unbox_usize(v_builder_1625_);
    lean_dec(v_builder_1625_);
    v_bb_boxed_1629_ = lean_unbox_usize(v_bb_1626_);
    lean_dec(v_bb_1626_);
    v_res_1630_ =
        lean_llvm_position_builder_at_end(v_ctx_1624_, v_builder_boxed_1628_, v_bb_boxed_1629_);
    return v_res_1630_;
}
pub unsafe fn l_LLVM_buildCall2___boxed(
    mut v_ctx_1638_: *mut LeanObject,
    mut v_builder_1639_: *mut LeanObject,
    mut v_ty_1640_: *mut LeanObject,
    mut v_fn_1641_: *mut LeanObject,
    mut v_args_1642_: *mut LeanObject,
    mut v_name_1643_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1645_: usize = 0;
    let mut v_builder_boxed_1646_: usize = 0;
    let mut v_ty_boxed_1647_: usize = 0;
    let mut v_fn_boxed_1648_: usize = 0;
    let mut v_res_1649_: usize = 0;
    let mut v_r_1650_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1645_ = lean_unbox_usize(v_ctx_1638_);
    lean_dec(v_ctx_1638_);
    v_builder_boxed_1646_ = lean_unbox_usize(v_builder_1639_);
    lean_dec(v_builder_1639_);
    v_ty_boxed_1647_ = lean_unbox_usize(v_ty_1640_);
    lean_dec(v_ty_1640_);
    v_fn_boxed_1648_ = lean_unbox_usize(v_fn_1641_);
    lean_dec(v_fn_1641_);
    v_res_1649_ = lean_llvm_build_call2(
        v_ctx_boxed_1645_,
        v_builder_boxed_1646_,
        v_ty_boxed_1647_,
        v_fn_boxed_1648_,
        v_args_1642_,
        v_name_1643_,
    );
    lean_dec_ref(v_args_1642_);
    v_r_1650_ = lean_box_usize(v_res_1649_);
    return v_r_1650_;
}
pub unsafe fn l_LLVM_setTailCall___boxed(
    mut v_ctx_1655_: *mut LeanObject,
    mut v_fn_1656_: *mut LeanObject,
    mut v_istail_1657_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1659_: usize = 0;
    let mut v_fn_boxed_1660_: usize = 0;
    let mut v_istail_boxed_1661_: u8 = 0;
    let mut v_res_1662_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1659_ = lean_unbox_usize(v_ctx_1655_);
    lean_dec(v_ctx_1655_);
    v_fn_boxed_1660_ = lean_unbox_usize(v_fn_1656_);
    lean_dec(v_fn_1656_);
    v_istail_boxed_1661_ = (lean_unbox(v_istail_1657_) as u8);
    v_res_1662_ =
        lean_llvm_set_tail_call(v_ctx_boxed_1659_, v_fn_boxed_1660_, v_istail_boxed_1661_);
    return v_res_1662_;
}
pub unsafe fn l_LLVM_buildCondBr___boxed(
    mut v_ctx_1669_: *mut LeanObject,
    mut v_builder_1670_: *mut LeanObject,
    mut v_if___1671_: *mut LeanObject,
    mut v_thenbb_1672_: *mut LeanObject,
    mut v_elsebb_1673_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1675_: usize = 0;
    let mut v_builder_boxed_1676_: usize = 0;
    let mut v_if___00boxed_1677_: usize = 0;
    let mut v_thenbb_boxed_1678_: usize = 0;
    let mut v_elsebb_boxed_1679_: usize = 0;
    let mut v_res_1680_: usize = 0;
    let mut v_r_1681_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1675_ = lean_unbox_usize(v_ctx_1669_);
    lean_dec(v_ctx_1669_);
    v_builder_boxed_1676_ = lean_unbox_usize(v_builder_1670_);
    lean_dec(v_builder_1670_);
    v_if___00boxed_1677_ = lean_unbox_usize(v_if___1671_);
    lean_dec(v_if___1671_);
    v_thenbb_boxed_1678_ = lean_unbox_usize(v_thenbb_1672_);
    lean_dec(v_thenbb_1672_);
    v_elsebb_boxed_1679_ = lean_unbox_usize(v_elsebb_1673_);
    lean_dec(v_elsebb_1673_);
    v_res_1680_ = lean_llvm_build_cond_br(
        v_ctx_boxed_1675_,
        v_builder_boxed_1676_,
        v_if___00boxed_1677_,
        v_thenbb_boxed_1678_,
        v_elsebb_boxed_1679_,
    );
    v_r_1681_ = lean_box_usize(v_res_1680_);
    return v_r_1681_;
}
pub unsafe fn l_LLVM_buildBr___boxed(
    mut v_ctx_1686_: *mut LeanObject,
    mut v_builder_1687_: *mut LeanObject,
    mut v_bb_1688_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1690_: usize = 0;
    let mut v_builder_boxed_1691_: usize = 0;
    let mut v_bb_boxed_1692_: usize = 0;
    let mut v_res_1693_: usize = 0;
    let mut v_r_1694_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1690_ = lean_unbox_usize(v_ctx_1686_);
    lean_dec(v_ctx_1686_);
    v_builder_boxed_1691_ = lean_unbox_usize(v_builder_1687_);
    lean_dec(v_builder_1687_);
    v_bb_boxed_1692_ = lean_unbox_usize(v_bb_1688_);
    lean_dec(v_bb_1688_);
    v_res_1693_ = lean_llvm_build_br(v_ctx_boxed_1690_, v_builder_boxed_1691_, v_bb_boxed_1692_);
    v_r_1694_ = lean_box_usize(v_res_1693_);
    return v_r_1694_;
}
pub unsafe fn l_LLVM_buildAlloca___boxed(
    mut v_ctx_1700_: *mut LeanObject,
    mut v_builder_1701_: *mut LeanObject,
    mut v_ty_1702_: *mut LeanObject,
    mut v_name_1703_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1705_: usize = 0;
    let mut v_builder_boxed_1706_: usize = 0;
    let mut v_ty_boxed_1707_: usize = 0;
    let mut v_res_1708_: usize = 0;
    let mut v_r_1709_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1705_ = lean_unbox_usize(v_ctx_1700_);
    lean_dec(v_ctx_1700_);
    v_builder_boxed_1706_ = lean_unbox_usize(v_builder_1701_);
    lean_dec(v_builder_1701_);
    v_ty_boxed_1707_ = lean_unbox_usize(v_ty_1702_);
    lean_dec(v_ty_1702_);
    v_res_1708_ = lean_llvm_build_alloca(
        v_ctx_boxed_1705_,
        v_builder_boxed_1706_,
        v_ty_boxed_1707_,
        v_name_1703_,
    );
    v_r_1709_ = lean_box_usize(v_res_1708_);
    return v_r_1709_;
}
pub unsafe fn l_LLVM_buildLoad2___boxed(
    mut v_ctx_1716_: *mut LeanObject,
    mut v_builder_1717_: *mut LeanObject,
    mut v_ty_1718_: *mut LeanObject,
    mut v_val_1719_: *mut LeanObject,
    mut v_name_1720_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1722_: usize = 0;
    let mut v_builder_boxed_1723_: usize = 0;
    let mut v_ty_boxed_1724_: usize = 0;
    let mut v_val_boxed_1725_: usize = 0;
    let mut v_res_1726_: usize = 0;
    let mut v_r_1727_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1722_ = lean_unbox_usize(v_ctx_1716_);
    lean_dec(v_ctx_1716_);
    v_builder_boxed_1723_ = lean_unbox_usize(v_builder_1717_);
    lean_dec(v_builder_1717_);
    v_ty_boxed_1724_ = lean_unbox_usize(v_ty_1718_);
    lean_dec(v_ty_1718_);
    v_val_boxed_1725_ = lean_unbox_usize(v_val_1719_);
    lean_dec(v_val_1719_);
    v_res_1726_ = lean_llvm_build_load2(
        v_ctx_boxed_1722_,
        v_builder_boxed_1723_,
        v_ty_boxed_1724_,
        v_val_boxed_1725_,
        v_name_1720_,
    );
    v_r_1727_ = lean_box_usize(v_res_1726_);
    return v_r_1727_;
}
pub unsafe fn l_LLVM_buildStore___boxed(
    mut v_ctx_1733_: *mut LeanObject,
    mut v_builder_1734_: *mut LeanObject,
    mut v_val_1735_: *mut LeanObject,
    mut v_store__loc__ptr_1736_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1738_: usize = 0;
    let mut v_builder_boxed_1739_: usize = 0;
    let mut v_val_boxed_1740_: usize = 0;
    let mut v_store__loc__ptr_boxed_1741_: usize = 0;
    let mut v_res_1742_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1738_ = lean_unbox_usize(v_ctx_1733_);
    lean_dec(v_ctx_1733_);
    v_builder_boxed_1739_ = lean_unbox_usize(v_builder_1734_);
    lean_dec(v_builder_1734_);
    v_val_boxed_1740_ = lean_unbox_usize(v_val_1735_);
    lean_dec(v_val_1735_);
    v_store__loc__ptr_boxed_1741_ = lean_unbox_usize(v_store__loc__ptr_1736_);
    lean_dec(v_store__loc__ptr_1736_);
    v_res_1742_ = lean_llvm_build_store(
        v_ctx_boxed_1738_,
        v_builder_boxed_1739_,
        v_val_boxed_1740_,
        v_store__loc__ptr_boxed_1741_,
    );
    return v_res_1742_;
}
pub unsafe fn l_LLVM_buildRet___boxed(
    mut v_ctx_1747_: *mut LeanObject,
    mut v_builder_1748_: *mut LeanObject,
    mut v_val_1749_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1751_: usize = 0;
    let mut v_builder_boxed_1752_: usize = 0;
    let mut v_val_boxed_1753_: usize = 0;
    let mut v_res_1754_: usize = 0;
    let mut v_r_1755_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1751_ = lean_unbox_usize(v_ctx_1747_);
    lean_dec(v_ctx_1747_);
    v_builder_boxed_1752_ = lean_unbox_usize(v_builder_1748_);
    lean_dec(v_builder_1748_);
    v_val_boxed_1753_ = lean_unbox_usize(v_val_1749_);
    lean_dec(v_val_1749_);
    v_res_1754_ = lean_llvm_build_ret(v_ctx_boxed_1751_, v_builder_boxed_1752_, v_val_boxed_1753_);
    v_r_1755_ = lean_box_usize(v_res_1754_);
    return v_r_1755_;
}
pub unsafe fn l_LLVM_buildUnreachable___boxed(
    mut v_ctx_1759_: *mut LeanObject,
    mut v_builder_1760_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1762_: usize = 0;
    let mut v_builder_boxed_1763_: usize = 0;
    let mut v_res_1764_: usize = 0;
    let mut v_r_1765_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1762_ = lean_unbox_usize(v_ctx_1759_);
    lean_dec(v_ctx_1759_);
    v_builder_boxed_1763_ = lean_unbox_usize(v_builder_1760_);
    lean_dec(v_builder_1760_);
    v_res_1764_ = lean_llvm_build_unreachable(v_ctx_boxed_1762_, v_builder_boxed_1763_);
    v_r_1765_ = lean_box_usize(v_res_1764_);
    return v_r_1765_;
}
pub unsafe fn l_LLVM_buildGEP2___boxed(
    mut v_ctx_1773_: *mut LeanObject,
    mut v_builder_1774_: *mut LeanObject,
    mut v_ty_1775_: *mut LeanObject,
    mut v_base_1776_: *mut LeanObject,
    mut v_ixs_1777_: *mut LeanObject,
    mut v_name_1778_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1780_: usize = 0;
    let mut v_builder_boxed_1781_: usize = 0;
    let mut v_ty_boxed_1782_: usize = 0;
    let mut v_base_boxed_1783_: usize = 0;
    let mut v_res_1784_: usize = 0;
    let mut v_r_1785_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1780_ = lean_unbox_usize(v_ctx_1773_);
    lean_dec(v_ctx_1773_);
    v_builder_boxed_1781_ = lean_unbox_usize(v_builder_1774_);
    lean_dec(v_builder_1774_);
    v_ty_boxed_1782_ = lean_unbox_usize(v_ty_1775_);
    lean_dec(v_ty_1775_);
    v_base_boxed_1783_ = lean_unbox_usize(v_base_1776_);
    lean_dec(v_base_1776_);
    v_res_1784_ = lean_llvm_build_gep2(
        v_ctx_boxed_1780_,
        v_builder_boxed_1781_,
        v_ty_boxed_1782_,
        v_base_boxed_1783_,
        v_ixs_1777_,
        v_name_1778_,
    );
    lean_dec_ref(v_ixs_1777_);
    v_r_1785_ = lean_box_usize(v_res_1784_);
    return v_r_1785_;
}
pub unsafe fn l_LLVM_buildInBoundsGEP2___boxed(
    mut v_ctx_1793_: *mut LeanObject,
    mut v_builder_1794_: *mut LeanObject,
    mut v_ty_1795_: *mut LeanObject,
    mut v_base_1796_: *mut LeanObject,
    mut v_ixs_1797_: *mut LeanObject,
    mut v_name_1798_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1800_: usize = 0;
    let mut v_builder_boxed_1801_: usize = 0;
    let mut v_ty_boxed_1802_: usize = 0;
    let mut v_base_boxed_1803_: usize = 0;
    let mut v_res_1804_: usize = 0;
    let mut v_r_1805_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1800_ = lean_unbox_usize(v_ctx_1793_);
    lean_dec(v_ctx_1793_);
    v_builder_boxed_1801_ = lean_unbox_usize(v_builder_1794_);
    lean_dec(v_builder_1794_);
    v_ty_boxed_1802_ = lean_unbox_usize(v_ty_1795_);
    lean_dec(v_ty_1795_);
    v_base_boxed_1803_ = lean_unbox_usize(v_base_1796_);
    lean_dec(v_base_1796_);
    v_res_1804_ = lean_llvm_build_inbounds_gep2(
        v_ctx_boxed_1800_,
        v_builder_boxed_1801_,
        v_ty_boxed_1802_,
        v_base_boxed_1803_,
        v_ixs_1797_,
        v_name_1798_,
    );
    lean_dec_ref(v_ixs_1797_);
    v_r_1805_ = lean_box_usize(v_res_1804_);
    return v_r_1805_;
}
pub unsafe fn l_LLVM_buildSext___boxed(
    mut v_ctx_1812_: *mut LeanObject,
    mut v_builder_1813_: *mut LeanObject,
    mut v_val_1814_: *mut LeanObject,
    mut v_destTy_1815_: *mut LeanObject,
    mut v_name_1816_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1818_: usize = 0;
    let mut v_builder_boxed_1819_: usize = 0;
    let mut v_val_boxed_1820_: usize = 0;
    let mut v_destTy_boxed_1821_: usize = 0;
    let mut v_res_1822_: usize = 0;
    let mut v_r_1823_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1818_ = lean_unbox_usize(v_ctx_1812_);
    lean_dec(v_ctx_1812_);
    v_builder_boxed_1819_ = lean_unbox_usize(v_builder_1813_);
    lean_dec(v_builder_1813_);
    v_val_boxed_1820_ = lean_unbox_usize(v_val_1814_);
    lean_dec(v_val_1814_);
    v_destTy_boxed_1821_ = lean_unbox_usize(v_destTy_1815_);
    lean_dec(v_destTy_1815_);
    v_res_1822_ = lean_llvm_build_sext(
        v_ctx_boxed_1818_,
        v_builder_boxed_1819_,
        v_val_boxed_1820_,
        v_destTy_boxed_1821_,
        v_name_1816_,
    );
    v_r_1823_ = lean_box_usize(v_res_1822_);
    return v_r_1823_;
}
pub unsafe fn l_LLVM_buildZext___boxed(
    mut v_ctx_1830_: *mut LeanObject,
    mut v_builder_1831_: *mut LeanObject,
    mut v_val_1832_: *mut LeanObject,
    mut v_destTy_1833_: *mut LeanObject,
    mut v_name_1834_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1836_: usize = 0;
    let mut v_builder_boxed_1837_: usize = 0;
    let mut v_val_boxed_1838_: usize = 0;
    let mut v_destTy_boxed_1839_: usize = 0;
    let mut v_res_1840_: usize = 0;
    let mut v_r_1841_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1836_ = lean_unbox_usize(v_ctx_1830_);
    lean_dec(v_ctx_1830_);
    v_builder_boxed_1837_ = lean_unbox_usize(v_builder_1831_);
    lean_dec(v_builder_1831_);
    v_val_boxed_1838_ = lean_unbox_usize(v_val_1832_);
    lean_dec(v_val_1832_);
    v_destTy_boxed_1839_ = lean_unbox_usize(v_destTy_1833_);
    lean_dec(v_destTy_1833_);
    v_res_1840_ = lean_llvm_build_zext(
        v_ctx_boxed_1836_,
        v_builder_boxed_1837_,
        v_val_boxed_1838_,
        v_destTy_boxed_1839_,
        v_name_1834_,
    );
    v_r_1841_ = lean_box_usize(v_res_1840_);
    return v_r_1841_;
}
pub unsafe fn l_LLVM_buildSextOrTrunc___boxed(
    mut v_ctx_1848_: *mut LeanObject,
    mut v_builder_1849_: *mut LeanObject,
    mut v_val_1850_: *mut LeanObject,
    mut v_destTy_1851_: *mut LeanObject,
    mut v_name_1852_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1854_: usize = 0;
    let mut v_builder_boxed_1855_: usize = 0;
    let mut v_val_boxed_1856_: usize = 0;
    let mut v_destTy_boxed_1857_: usize = 0;
    let mut v_res_1858_: usize = 0;
    let mut v_r_1859_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1854_ = lean_unbox_usize(v_ctx_1848_);
    lean_dec(v_ctx_1848_);
    v_builder_boxed_1855_ = lean_unbox_usize(v_builder_1849_);
    lean_dec(v_builder_1849_);
    v_val_boxed_1856_ = lean_unbox_usize(v_val_1850_);
    lean_dec(v_val_1850_);
    v_destTy_boxed_1857_ = lean_unbox_usize(v_destTy_1851_);
    lean_dec(v_destTy_1851_);
    v_res_1858_ = lean_llvm_build_sext_or_trunc(
        v_ctx_boxed_1854_,
        v_builder_boxed_1855_,
        v_val_boxed_1856_,
        v_destTy_boxed_1857_,
        v_name_1852_,
    );
    v_r_1859_ = lean_box_usize(v_res_1858_);
    return v_r_1859_;
}
pub unsafe fn l_LLVM_buildSwitch___boxed(
    mut v_ctx_1866_: *mut LeanObject,
    mut v_builder_1867_: *mut LeanObject,
    mut v_val_1868_: *mut LeanObject,
    mut v_elseBB_1869_: *mut LeanObject,
    mut v_numCasesHint_1870_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1872_: usize = 0;
    let mut v_builder_boxed_1873_: usize = 0;
    let mut v_val_boxed_1874_: usize = 0;
    let mut v_elseBB_boxed_1875_: usize = 0;
    let mut v_numCasesHint_boxed_1876_: u64 = 0;
    let mut v_res_1877_: usize = 0;
    let mut v_r_1878_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1872_ = lean_unbox_usize(v_ctx_1866_);
    lean_dec(v_ctx_1866_);
    v_builder_boxed_1873_ = lean_unbox_usize(v_builder_1867_);
    lean_dec(v_builder_1867_);
    v_val_boxed_1874_ = lean_unbox_usize(v_val_1868_);
    lean_dec(v_val_1868_);
    v_elseBB_boxed_1875_ = lean_unbox_usize(v_elseBB_1869_);
    lean_dec(v_elseBB_1869_);
    v_numCasesHint_boxed_1876_ = lean_unbox_uint64(v_numCasesHint_1870_);
    lean_dec_ref(v_numCasesHint_1870_);
    v_res_1877_ = lean_llvm_build_switch(
        v_ctx_boxed_1872_,
        v_builder_boxed_1873_,
        v_val_boxed_1874_,
        v_elseBB_boxed_1875_,
        v_numCasesHint_boxed_1876_,
    );
    v_r_1878_ = lean_box_usize(v_res_1877_);
    return v_r_1878_;
}
pub unsafe fn l_LLVM_buildPtrToInt___boxed(
    mut v_ctx_1885_: *mut LeanObject,
    mut v_builder_1886_: *mut LeanObject,
    mut v_ptr_1887_: *mut LeanObject,
    mut v_destTy_1888_: *mut LeanObject,
    mut v_name_1889_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1891_: usize = 0;
    let mut v_builder_boxed_1892_: usize = 0;
    let mut v_ptr_boxed_1893_: usize = 0;
    let mut v_destTy_boxed_1894_: usize = 0;
    let mut v_res_1895_: usize = 0;
    let mut v_r_1896_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1891_ = lean_unbox_usize(v_ctx_1885_);
    lean_dec(v_ctx_1885_);
    v_builder_boxed_1892_ = lean_unbox_usize(v_builder_1886_);
    lean_dec(v_builder_1886_);
    v_ptr_boxed_1893_ = lean_unbox_usize(v_ptr_1887_);
    lean_dec(v_ptr_1887_);
    v_destTy_boxed_1894_ = lean_unbox_usize(v_destTy_1888_);
    lean_dec(v_destTy_1888_);
    v_res_1895_ = lean_llvm_build_ptr_to_int(
        v_ctx_boxed_1891_,
        v_builder_boxed_1892_,
        v_ptr_boxed_1893_,
        v_destTy_boxed_1894_,
        v_name_1889_,
    );
    v_r_1896_ = lean_box_usize(v_res_1895_);
    return v_r_1896_;
}
pub unsafe fn l_LLVM_buildMul___boxed(
    mut v_ctx_1903_: *mut LeanObject,
    mut v_builder_1904_: *mut LeanObject,
    mut v_x_1905_: *mut LeanObject,
    mut v_y_1906_: *mut LeanObject,
    mut v_name_1907_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1909_: usize = 0;
    let mut v_builder_boxed_1910_: usize = 0;
    let mut v_x_boxed_1911_: usize = 0;
    let mut v_y_boxed_1912_: usize = 0;
    let mut v_res_1913_: usize = 0;
    let mut v_r_1914_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1909_ = lean_unbox_usize(v_ctx_1903_);
    lean_dec(v_ctx_1903_);
    v_builder_boxed_1910_ = lean_unbox_usize(v_builder_1904_);
    lean_dec(v_builder_1904_);
    v_x_boxed_1911_ = lean_unbox_usize(v_x_1905_);
    lean_dec(v_x_1905_);
    v_y_boxed_1912_ = lean_unbox_usize(v_y_1906_);
    lean_dec(v_y_1906_);
    v_res_1913_ = lean_llvm_build_mul(
        v_ctx_boxed_1909_,
        v_builder_boxed_1910_,
        v_x_boxed_1911_,
        v_y_boxed_1912_,
        v_name_1907_,
    );
    v_r_1914_ = lean_box_usize(v_res_1913_);
    return v_r_1914_;
}
pub unsafe fn l_LLVM_buildAdd___boxed(
    mut v_ctx_1921_: *mut LeanObject,
    mut v_builder_1922_: *mut LeanObject,
    mut v_x_1923_: *mut LeanObject,
    mut v_y_1924_: *mut LeanObject,
    mut v_name_1925_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1927_: usize = 0;
    let mut v_builder_boxed_1928_: usize = 0;
    let mut v_x_boxed_1929_: usize = 0;
    let mut v_y_boxed_1930_: usize = 0;
    let mut v_res_1931_: usize = 0;
    let mut v_r_1932_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1927_ = lean_unbox_usize(v_ctx_1921_);
    lean_dec(v_ctx_1921_);
    v_builder_boxed_1928_ = lean_unbox_usize(v_builder_1922_);
    lean_dec(v_builder_1922_);
    v_x_boxed_1929_ = lean_unbox_usize(v_x_1923_);
    lean_dec(v_x_1923_);
    v_y_boxed_1930_ = lean_unbox_usize(v_y_1924_);
    lean_dec(v_y_1924_);
    v_res_1931_ = lean_llvm_build_add(
        v_ctx_boxed_1927_,
        v_builder_boxed_1928_,
        v_x_boxed_1929_,
        v_y_boxed_1930_,
        v_name_1925_,
    );
    v_r_1932_ = lean_box_usize(v_res_1931_);
    return v_r_1932_;
}
pub unsafe fn l_LLVM_buildSub___boxed(
    mut v_ctx_1939_: *mut LeanObject,
    mut v_builder_1940_: *mut LeanObject,
    mut v_x_1941_: *mut LeanObject,
    mut v_y_1942_: *mut LeanObject,
    mut v_name_1943_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1945_: usize = 0;
    let mut v_builder_boxed_1946_: usize = 0;
    let mut v_x_boxed_1947_: usize = 0;
    let mut v_y_boxed_1948_: usize = 0;
    let mut v_res_1949_: usize = 0;
    let mut v_r_1950_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1945_ = lean_unbox_usize(v_ctx_1939_);
    lean_dec(v_ctx_1939_);
    v_builder_boxed_1946_ = lean_unbox_usize(v_builder_1940_);
    lean_dec(v_builder_1940_);
    v_x_boxed_1947_ = lean_unbox_usize(v_x_1941_);
    lean_dec(v_x_1941_);
    v_y_boxed_1948_ = lean_unbox_usize(v_y_1942_);
    lean_dec(v_y_1942_);
    v_res_1949_ = lean_llvm_build_sub(
        v_ctx_boxed_1945_,
        v_builder_boxed_1946_,
        v_x_boxed_1947_,
        v_y_boxed_1948_,
        v_name_1943_,
    );
    v_r_1950_ = lean_box_usize(v_res_1949_);
    return v_r_1950_;
}
pub unsafe fn l_LLVM_buildNot___boxed(
    mut v_ctx_1956_: *mut LeanObject,
    mut v_builder_1957_: *mut LeanObject,
    mut v_x_1958_: *mut LeanObject,
    mut v_name_1959_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1961_: usize = 0;
    let mut v_builder_boxed_1962_: usize = 0;
    let mut v_x_boxed_1963_: usize = 0;
    let mut v_res_1964_: usize = 0;
    let mut v_r_1965_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1961_ = lean_unbox_usize(v_ctx_1956_);
    lean_dec(v_ctx_1956_);
    v_builder_boxed_1962_ = lean_unbox_usize(v_builder_1957_);
    lean_dec(v_builder_1957_);
    v_x_boxed_1963_ = lean_unbox_usize(v_x_1958_);
    lean_dec(v_x_1958_);
    v_res_1964_ = lean_llvm_build_not(
        v_ctx_boxed_1961_,
        v_builder_boxed_1962_,
        v_x_boxed_1963_,
        v_name_1959_,
    );
    v_r_1965_ = lean_box_usize(v_res_1964_);
    return v_r_1965_;
}
pub unsafe fn l_LLVM_buildICmp___boxed(
    mut v_ctx_1973_: *mut LeanObject,
    mut v_builder_1974_: *mut LeanObject,
    mut v_predicate_1975_: *mut LeanObject,
    mut v_x_1976_: *mut LeanObject,
    mut v_y_1977_: *mut LeanObject,
    mut v_name_1978_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1980_: usize = 0;
    let mut v_builder_boxed_1981_: usize = 0;
    let mut v_predicate_boxed_1982_: u64 = 0;
    let mut v_x_boxed_1983_: usize = 0;
    let mut v_y_boxed_1984_: usize = 0;
    let mut v_res_1985_: usize = 0;
    let mut v_r_1986_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1980_ = lean_unbox_usize(v_ctx_1973_);
    lean_dec(v_ctx_1973_);
    v_builder_boxed_1981_ = lean_unbox_usize(v_builder_1974_);
    lean_dec(v_builder_1974_);
    v_predicate_boxed_1982_ = lean_unbox_uint64(v_predicate_1975_);
    lean_dec_ref(v_predicate_1975_);
    v_x_boxed_1983_ = lean_unbox_usize(v_x_1976_);
    lean_dec(v_x_1976_);
    v_y_boxed_1984_ = lean_unbox_usize(v_y_1977_);
    lean_dec(v_y_1977_);
    v_res_1985_ = lean_llvm_build_icmp(
        v_ctx_boxed_1980_,
        v_builder_boxed_1981_,
        v_predicate_boxed_1982_,
        v_x_boxed_1983_,
        v_y_boxed_1984_,
        v_name_1978_,
    );
    v_r_1986_ = lean_box_usize(v_res_1985_);
    return v_r_1986_;
}
pub unsafe fn l_LLVM_addCase___boxed(
    mut v_ctx_1992_: *mut LeanObject,
    mut v_switch_1993_: *mut LeanObject,
    mut v_onVal_1994_: *mut LeanObject,
    mut v_destBB_1995_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_1997_: usize = 0;
    let mut v_switch_boxed_1998_: usize = 0;
    let mut v_onVal_boxed_1999_: usize = 0;
    let mut v_destBB_boxed_2000_: usize = 0;
    let mut v_res_2001_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1997_ = lean_unbox_usize(v_ctx_1992_);
    lean_dec(v_ctx_1992_);
    v_switch_boxed_1998_ = lean_unbox_usize(v_switch_1993_);
    lean_dec(v_switch_1993_);
    v_onVal_boxed_1999_ = lean_unbox_usize(v_onVal_1994_);
    lean_dec(v_onVal_1994_);
    v_destBB_boxed_2000_ = lean_unbox_usize(v_destBB_1995_);
    lean_dec(v_destBB_1995_);
    v_res_2001_ = lean_llvm_add_case(
        v_ctx_boxed_1997_,
        v_switch_boxed_1998_,
        v_onVal_boxed_1999_,
        v_destBB_boxed_2000_,
    );
    return v_res_2001_;
}
pub unsafe fn l_LLVM_getInsertBlock___boxed(
    mut v_Context_00___x40_Lean_Compiler_IR_LLVMBindings_924321998____hygCtx___hyg_2006_: *mut LeanObject,
    mut v_ctx_2007_: *mut LeanObject,
    mut v_builder_2008_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_builder_boxed_2010_: usize = 0;
    let mut v_res_2011_: usize = 0;
    let mut v_r_2012_: *mut LeanObject = core::ptr::null_mut();
    v_builder_boxed_2010_ = lean_unbox_usize(v_builder_2008_);
    lean_dec(v_builder_2008_);
    v_res_2011_ = lean_llvm_get_insert_block(v_ctx_2007_, v_builder_boxed_2010_);
    v_r_2012_ = lean_box_usize(v_res_2011_);
    return v_r_2012_;
}
pub unsafe fn l_LLVM_clearInsertionPosition___boxed(
    mut v_Context_00___x40_Lean_Compiler_IR_LLVMBindings_1700267677____hygCtx___hyg_2017_: *mut LeanObject,
    mut v_ctx_2018_: *mut LeanObject,
    mut v_builder_2019_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_builder_boxed_2021_: usize = 0;
    let mut v_res_2022_: *mut LeanObject = core::ptr::null_mut();
    v_builder_boxed_2021_ = lean_unbox_usize(v_builder_2019_);
    lean_dec(v_builder_2019_);
    v_res_2022_ = lean_llvm_clear_insertion_position(v_ctx_2018_, v_builder_boxed_2021_);
    return v_res_2022_;
}
pub unsafe fn l_LLVM_getBasicBlockParent___boxed(
    mut v_ctx_2026_: *mut LeanObject,
    mut v_bb_2027_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2029_: usize = 0;
    let mut v_bb_boxed_2030_: usize = 0;
    let mut v_res_2031_: usize = 0;
    let mut v_r_2032_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2029_ = lean_unbox_usize(v_ctx_2026_);
    lean_dec(v_ctx_2026_);
    v_bb_boxed_2030_ = lean_unbox_usize(v_bb_2027_);
    lean_dec(v_bb_2027_);
    v_res_2031_ = lean_llvm_get_basic_block_parent(v_ctx_boxed_2029_, v_bb_boxed_2030_);
    v_r_2032_ = lean_box_usize(v_res_2031_);
    return v_r_2032_;
}
pub unsafe fn l_LLVM_typeOf___boxed(
    mut v_ctx_2036_: *mut LeanObject,
    mut v_val_2037_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2039_: usize = 0;
    let mut v_val_boxed_2040_: usize = 0;
    let mut v_res_2041_: usize = 0;
    let mut v_r_2042_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2039_ = lean_unbox_usize(v_ctx_2036_);
    lean_dec(v_ctx_2036_);
    v_val_boxed_2040_ = lean_unbox_usize(v_val_2037_);
    lean_dec(v_val_2037_);
    v_res_2041_ = lean_llvm_type_of(v_ctx_boxed_2039_, v_val_boxed_2040_);
    v_r_2042_ = lean_box_usize(v_res_2041_);
    return v_r_2042_;
}
pub unsafe fn l_LLVM_constInt___boxed(
    mut v_ctx_2048_: *mut LeanObject,
    mut v_intty_2049_: *mut LeanObject,
    mut v_value_2050_: *mut LeanObject,
    mut v_signExtend_2051_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2053_: usize = 0;
    let mut v_intty_boxed_2054_: usize = 0;
    let mut v_value_boxed_2055_: u64 = 0;
    let mut v_signExtend_boxed_2056_: u8 = 0;
    let mut v_res_2057_: usize = 0;
    let mut v_r_2058_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2053_ = lean_unbox_usize(v_ctx_2048_);
    lean_dec(v_ctx_2048_);
    v_intty_boxed_2054_ = lean_unbox_usize(v_intty_2049_);
    lean_dec(v_intty_2049_);
    v_value_boxed_2055_ = lean_unbox_uint64(v_value_2050_);
    lean_dec_ref(v_value_2050_);
    v_signExtend_boxed_2056_ = (lean_unbox(v_signExtend_2051_) as u8);
    v_res_2057_ = lean_llvm_const_int(
        v_ctx_boxed_2053_,
        v_intty_boxed_2054_,
        v_value_boxed_2055_,
        v_signExtend_boxed_2056_,
    );
    v_r_2058_ = lean_box_usize(v_res_2057_);
    return v_r_2058_;
}
pub unsafe fn l_LLVM_printModuletoString___boxed(
    mut v_ctx_2062_: *mut LeanObject,
    mut v_mod_2063_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2065_: usize = 0;
    let mut v_mod_boxed_2066_: usize = 0;
    let mut v_res_2067_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2065_ = lean_unbox_usize(v_ctx_2062_);
    lean_dec(v_ctx_2062_);
    v_mod_boxed_2066_ = lean_unbox_usize(v_mod_2063_);
    lean_dec(v_mod_2063_);
    v_res_2067_ = lean_llvm_print_module_to_string(v_ctx_boxed_2065_, v_mod_boxed_2066_);
    return v_res_2067_;
}
pub unsafe fn l_LLVM_printModuletoFile___boxed(
    mut v_ctx_2072_: *mut LeanObject,
    mut v_mod_2073_: *mut LeanObject,
    mut v_file_2074_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2076_: usize = 0;
    let mut v_mod_boxed_2077_: usize = 0;
    let mut v_res_2078_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2076_ = lean_unbox_usize(v_ctx_2072_);
    lean_dec(v_ctx_2072_);
    v_mod_boxed_2077_ = lean_unbox_usize(v_mod_2073_);
    lean_dec(v_mod_2073_);
    v_res_2078_ =
        lean_llvm_print_module_to_file(v_ctx_boxed_2076_, v_mod_boxed_2077_, v_file_2074_);
    lean_dec_ref(v_file_2074_);
    return v_res_2078_;
}
pub unsafe fn l_LLVM_countParams___boxed(
    mut v_ctx_2082_: *mut LeanObject,
    mut v_fn_2083_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2085_: usize = 0;
    let mut v_fn_boxed_2086_: usize = 0;
    let mut v_res_2087_: u64 = 0;
    let mut v_r_2088_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2085_ = lean_unbox_usize(v_ctx_2082_);
    lean_dec(v_ctx_2082_);
    v_fn_boxed_2086_ = lean_unbox_usize(v_fn_2083_);
    lean_dec(v_fn_2083_);
    v_res_2087_ = llvm_count_params(v_ctx_boxed_2085_, v_fn_boxed_2086_);
    v_r_2088_ = lean_box_uint64(v_res_2087_);
    return v_r_2088_;
}
pub unsafe fn l_LLVM_getParam___boxed(
    mut v_ctx_2093_: *mut LeanObject,
    mut v_fn_2094_: *mut LeanObject,
    mut v_ix_2095_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2097_: usize = 0;
    let mut v_fn_boxed_2098_: usize = 0;
    let mut v_ix_boxed_2099_: u64 = 0;
    let mut v_res_2100_: usize = 0;
    let mut v_r_2101_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2097_ = lean_unbox_usize(v_ctx_2093_);
    lean_dec(v_ctx_2093_);
    v_fn_boxed_2098_ = lean_unbox_usize(v_fn_2094_);
    lean_dec(v_fn_2094_);
    v_ix_boxed_2099_ = lean_unbox_uint64(v_ix_2095_);
    lean_dec_ref(v_ix_2095_);
    v_res_2100_ = llvm_get_param(v_ctx_boxed_2097_, v_fn_boxed_2098_, v_ix_boxed_2099_);
    v_r_2101_ = lean_box_usize(v_res_2100_);
    return v_r_2101_;
}
pub unsafe fn l_LLVM_createMemoryBufferWithContentsOfFile___boxed(
    mut v_ctx_2105_: *mut LeanObject,
    mut v_path_2106_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2108_: usize = 0;
    let mut v_res_2109_: usize = 0;
    let mut v_r_2110_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2108_ = lean_unbox_usize(v_ctx_2105_);
    lean_dec(v_ctx_2105_);
    v_res_2109_ =
        lean_llvm_create_memory_buffer_with_contents_of_file(v_ctx_boxed_2108_, v_path_2106_);
    lean_dec_ref(v_path_2106_);
    v_r_2110_ = lean_box_usize(v_res_2109_);
    return v_r_2110_;
}
pub unsafe fn l_LLVM_parseBitcode___boxed(
    mut v_ctx_2114_: *mut LeanObject,
    mut v_membuf_2115_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2117_: usize = 0;
    let mut v_membuf_boxed_2118_: usize = 0;
    let mut v_res_2119_: usize = 0;
    let mut v_r_2120_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2117_ = lean_unbox_usize(v_ctx_2114_);
    lean_dec(v_ctx_2114_);
    v_membuf_boxed_2118_ = lean_unbox_usize(v_membuf_2115_);
    lean_dec(v_membuf_2115_);
    v_res_2119_ = lean_llvm_parse_bitcode(v_ctx_boxed_2117_, v_membuf_boxed_2118_);
    v_r_2120_ = lean_box_usize(v_res_2119_);
    return v_r_2120_;
}
pub unsafe fn l_LLVM_linkModules___boxed(
    mut v_ctx_2125_: *mut LeanObject,
    mut v_dest_2126_: *mut LeanObject,
    mut v_src_2127_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2129_: usize = 0;
    let mut v_dest_boxed_2130_: usize = 0;
    let mut v_src_boxed_2131_: usize = 0;
    let mut v_res_2132_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2129_ = lean_unbox_usize(v_ctx_2125_);
    lean_dec(v_ctx_2125_);
    v_dest_boxed_2130_ = lean_unbox_usize(v_dest_2126_);
    lean_dec(v_dest_2126_);
    v_src_boxed_2131_ = lean_unbox_usize(v_src_2127_);
    lean_dec(v_src_2127_);
    v_res_2132_ = lean_llvm_link_modules(v_ctx_boxed_2129_, v_dest_boxed_2130_, v_src_boxed_2131_);
    return v_res_2132_;
}
pub unsafe fn l_LLVM_getDefaultTargetTriple___boxed(
    mut v_a_00___x40___internal___hyg_2134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2135_: *mut LeanObject = core::ptr::null_mut();
    v_res_2135_ = lean_llvm_get_default_target_triple();
    return v_res_2135_;
}
pub unsafe fn l_LLVM_getTargetFromTriple___boxed(
    mut v_ctx_2139_: *mut LeanObject,
    mut v_triple_2140_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2142_: usize = 0;
    let mut v_res_2143_: usize = 0;
    let mut v_r_2144_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2142_ = lean_unbox_usize(v_ctx_2139_);
    lean_dec(v_ctx_2139_);
    v_res_2143_ = lean_llvm_get_target_from_triple(v_ctx_boxed_2142_, v_triple_2140_);
    lean_dec_ref(v_triple_2140_);
    v_r_2144_ = lean_box_usize(v_res_2143_);
    return v_r_2144_;
}
pub unsafe fn l_LLVM_createTargetMachine___boxed(
    mut v_ctx_2151_: *mut LeanObject,
    mut v_target_2152_: *mut LeanObject,
    mut v_tripleStr_2153_: *mut LeanObject,
    mut v_cpu_2154_: *mut LeanObject,
    mut v_features_2155_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2157_: usize = 0;
    let mut v_target_boxed_2158_: usize = 0;
    let mut v_res_2159_: usize = 0;
    let mut v_r_2160_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2157_ = lean_unbox_usize(v_ctx_2151_);
    lean_dec(v_ctx_2151_);
    v_target_boxed_2158_ = lean_unbox_usize(v_target_2152_);
    lean_dec(v_target_2152_);
    v_res_2159_ = lean_llvm_create_target_machine(
        v_ctx_boxed_2157_,
        v_target_boxed_2158_,
        v_tripleStr_2153_,
        v_cpu_2154_,
        v_features_2155_,
    );
    lean_dec_ref(v_features_2155_);
    lean_dec_ref(v_cpu_2154_);
    lean_dec_ref(v_tripleStr_2153_);
    v_r_2160_ = lean_box_usize(v_res_2159_);
    return v_r_2160_;
}
pub unsafe fn l_LLVM_targetMachineEmitToFile___boxed(
    mut v_ctx_2167_: *mut LeanObject,
    mut v_targetMachine_2168_: *mut LeanObject,
    mut v_module_2169_: *mut LeanObject,
    mut v_filepath_2170_: *mut LeanObject,
    mut v_codegenType_2171_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2173_: usize = 0;
    let mut v_targetMachine_boxed_2174_: usize = 0;
    let mut v_module_boxed_2175_: usize = 0;
    let mut v_codegenType_boxed_2176_: u64 = 0;
    let mut v_res_2177_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2173_ = lean_unbox_usize(v_ctx_2167_);
    lean_dec(v_ctx_2167_);
    v_targetMachine_boxed_2174_ = lean_unbox_usize(v_targetMachine_2168_);
    lean_dec(v_targetMachine_2168_);
    v_module_boxed_2175_ = lean_unbox_usize(v_module_2169_);
    lean_dec(v_module_2169_);
    v_codegenType_boxed_2176_ = lean_unbox_uint64(v_codegenType_2171_);
    lean_dec_ref(v_codegenType_2171_);
    v_res_2177_ = lean_llvm_target_machine_emit_to_file(
        v_ctx_boxed_2173_,
        v_targetMachine_boxed_2174_,
        v_module_boxed_2175_,
        v_filepath_2170_,
        v_codegenType_boxed_2176_,
    );
    lean_dec_ref(v_filepath_2170_);
    return v_res_2177_;
}
pub unsafe fn l_LLVM_disposeTargetMachine___boxed(
    mut v_ctx_2181_: *mut LeanObject,
    mut v_tm_2182_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2184_: usize = 0;
    let mut v_tm_boxed_2185_: usize = 0;
    let mut v_res_2186_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2184_ = lean_unbox_usize(v_ctx_2181_);
    lean_dec(v_ctx_2181_);
    v_tm_boxed_2185_ = lean_unbox_usize(v_tm_2182_);
    lean_dec(v_tm_2182_);
    v_res_2186_ = lean_llvm_dispose_target_machine(v_ctx_boxed_2184_, v_tm_boxed_2185_);
    return v_res_2186_;
}
pub unsafe fn l_LLVM_disposeModule___boxed(
    mut v_ctx_2190_: *mut LeanObject,
    mut v_m_2191_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2193_: usize = 0;
    let mut v_m_boxed_2194_: usize = 0;
    let mut v_res_2195_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2193_ = lean_unbox_usize(v_ctx_2190_);
    lean_dec(v_ctx_2190_);
    v_m_boxed_2194_ = lean_unbox_usize(v_m_2191_);
    lean_dec(v_m_2191_);
    v_res_2195_ = lean_llvm_dispose_module(v_ctx_boxed_2193_, v_m_boxed_2194_);
    return v_res_2195_;
}
pub unsafe fn l_LLVM_verifyModule___boxed(
    mut v_ctx_2199_: *mut LeanObject,
    mut v_m_2200_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2202_: usize = 0;
    let mut v_m_boxed_2203_: usize = 0;
    let mut v_res_2204_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2202_ = lean_unbox_usize(v_ctx_2199_);
    lean_dec(v_ctx_2199_);
    v_m_boxed_2203_ = lean_unbox_usize(v_m_2200_);
    lean_dec(v_m_2200_);
    v_res_2204_ = lean_llvm_verify_module(v_ctx_boxed_2202_, v_m_boxed_2203_);
    return v_res_2204_;
}
pub unsafe fn l_LLVM_createStringAttribute___boxed(
    mut v_ctx_2209_: *mut LeanObject,
    mut v_key_2210_: *mut LeanObject,
    mut v_value_2211_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2213_: usize = 0;
    let mut v_res_2214_: usize = 0;
    let mut v_r_2215_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2213_ = lean_unbox_usize(v_ctx_2209_);
    lean_dec(v_ctx_2209_);
    v_res_2214_ = lean_llvm_create_string_attribute(v_ctx_boxed_2213_, v_key_2210_, v_value_2211_);
    v_r_2215_ = lean_box_usize(v_res_2214_);
    return v_r_2215_;
}
pub unsafe fn l_LLVM_addAttributeAtIndex___boxed(
    mut v_ctx_2221_: *mut LeanObject,
    mut v_fn_2222_: *mut LeanObject,
    mut v_idx_2223_: *mut LeanObject,
    mut v_attr_2224_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2226_: usize = 0;
    let mut v_fn_boxed_2227_: usize = 0;
    let mut v_idx_boxed_2228_: u64 = 0;
    let mut v_attr_boxed_2229_: usize = 0;
    let mut v_res_2230_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2226_ = lean_unbox_usize(v_ctx_2221_);
    lean_dec(v_ctx_2221_);
    v_fn_boxed_2227_ = lean_unbox_usize(v_fn_2222_);
    lean_dec(v_fn_2222_);
    v_idx_boxed_2228_ = lean_unbox_uint64(v_idx_2223_);
    lean_dec_ref(v_idx_2223_);
    v_attr_boxed_2229_ = lean_unbox_usize(v_attr_2224_);
    lean_dec(v_attr_2224_);
    v_res_2230_ = lean_llvm_add_attribute_at_index(
        v_ctx_boxed_2226_,
        v_fn_boxed_2227_,
        v_idx_boxed_2228_,
        v_attr_boxed_2229_,
    );
    return v_res_2230_;
}
pub unsafe fn _init_l_LLVM_Visibility_default() -> u64 {
    let mut v___x_2231_: u64 = 0;
    v___x_2231_ = 0u64;
    return v___x_2231_;
}
pub unsafe fn _init_l_LLVM_Visibility_hidden() -> u64 {
    let mut v___x_2232_: u64 = 0;
    v___x_2232_ = 1u64;
    return v___x_2232_;
}
pub unsafe fn _init_l_LLVM_Visibility_protected() -> u64 {
    let mut v___x_2233_: u64 = 0;
    v___x_2233_ = 2u64;
    return v___x_2233_;
}
pub unsafe fn l_LLVM_setVisibility___boxed(
    mut v_ctx_2238_: *mut LeanObject,
    mut v_value_2239_: *mut LeanObject,
    mut v_visibility_2240_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2242_: usize = 0;
    let mut v_value_boxed_2243_: usize = 0;
    let mut v_visibility_boxed_2244_: u64 = 0;
    let mut v_res_2245_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2242_ = lean_unbox_usize(v_ctx_2238_);
    lean_dec(v_ctx_2238_);
    v_value_boxed_2243_ = lean_unbox_usize(v_value_2239_);
    lean_dec(v_value_2239_);
    v_visibility_boxed_2244_ = lean_unbox_uint64(v_visibility_2240_);
    lean_dec_ref(v_visibility_2240_);
    v_res_2245_ = lean_llvm_set_visibility(
        v_ctx_boxed_2242_,
        v_value_boxed_2243_,
        v_visibility_boxed_2244_,
    );
    return v_res_2245_;
}
pub unsafe fn _init_l_LLVM_DLLStorageClass_default() -> u64 {
    let mut v___x_2246_: u64 = 0;
    v___x_2246_ = 0u64;
    return v___x_2246_;
}
pub unsafe fn _init_l_LLVM_DLLStorageClass_import() -> u64 {
    let mut v___x_2247_: u64 = 0;
    v___x_2247_ = 1u64;
    return v___x_2247_;
}
pub unsafe fn _init_l_LLVM_DLLStorageClass_export() -> u64 {
    let mut v___x_2248_: u64 = 0;
    v___x_2248_ = 2u64;
    return v___x_2248_;
}
pub unsafe fn l_LLVM_setDLLStorageClass___boxed(
    mut v_ctx_2253_: *mut LeanObject,
    mut v_value_2254_: *mut LeanObject,
    mut v_dllStorageClass_2255_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2257_: usize = 0;
    let mut v_value_boxed_2258_: usize = 0;
    let mut v_dllStorageClass_boxed_2259_: u64 = 0;
    let mut v_res_2260_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2257_ = lean_unbox_usize(v_ctx_2253_);
    lean_dec(v_ctx_2253_);
    v_value_boxed_2258_ = lean_unbox_usize(v_value_2254_);
    lean_dec(v_value_2254_);
    v_dllStorageClass_boxed_2259_ = lean_unbox_uint64(v_dllStorageClass_2255_);
    lean_dec_ref(v_dllStorageClass_2255_);
    v_res_2260_ = lean_llvm_set_dll_storage_class(
        v_ctx_boxed_2257_,
        v_value_boxed_2258_,
        v_dllStorageClass_boxed_2259_,
    );
    return v_res_2260_;
}
pub unsafe fn _init_l_LLVM_Linkage_external() -> u64 {
    let mut v___x_2261_: u64 = 0;
    v___x_2261_ = 0u64;
    return v___x_2261_;
}
pub unsafe fn _init_l_LLVM_Linkage_availableExternally() -> u64 {
    let mut v___x_2262_: u64 = 0;
    v___x_2262_ = 1u64;
    return v___x_2262_;
}
pub unsafe fn _init_l_LLVM_Linkage_linkOnceAny() -> u64 {
    let mut v___x_2263_: u64 = 0;
    v___x_2263_ = 2u64;
    return v___x_2263_;
}
pub unsafe fn _init_l_LLVM_Linkage_linkOnceODR() -> u64 {
    let mut v___x_2264_: u64 = 0;
    v___x_2264_ = 3u64;
    return v___x_2264_;
}
pub unsafe fn _init_l_LLVM_Linkage_linkOnceODRAutoHide() -> u64 {
    let mut v___x_2265_: u64 = 0;
    v___x_2265_ = 4u64;
    return v___x_2265_;
}
pub unsafe fn _init_l_LLVM_Linkage_weakAny() -> u64 {
    let mut v___x_2266_: u64 = 0;
    v___x_2266_ = 5u64;
    return v___x_2266_;
}
pub unsafe fn _init_l_LLVM_Linkage_weakODR() -> u64 {
    let mut v___x_2267_: u64 = 0;
    v___x_2267_ = 6u64;
    return v___x_2267_;
}
pub unsafe fn _init_l_LLVM_Linkage_appending() -> u64 {
    let mut v___x_2268_: u64 = 0;
    v___x_2268_ = 7u64;
    return v___x_2268_;
}
pub unsafe fn _init_l_LLVM_Linkage_internal() -> u64 {
    let mut v___x_2269_: u64 = 0;
    v___x_2269_ = 8u64;
    return v___x_2269_;
}
pub unsafe fn _init_l_LLVM_Linkage_private() -> u64 {
    let mut v___x_2270_: u64 = 0;
    v___x_2270_ = 9u64;
    return v___x_2270_;
}
pub unsafe fn _init_l_LLVM_Linkage_dllImport() -> u64 {
    let mut v___x_2271_: u64 = 0;
    v___x_2271_ = 10u64;
    return v___x_2271_;
}
pub unsafe fn _init_l_LLVM_Linkage_dllExport() -> u64 {
    let mut v___x_2272_: u64 = 0;
    v___x_2272_ = 11u64;
    return v___x_2272_;
}
pub unsafe fn _init_l_LLVM_Linkage_externalWeak() -> u64 {
    let mut v___x_2273_: u64 = 0;
    v___x_2273_ = 12u64;
    return v___x_2273_;
}
pub unsafe fn _init_l_LLVM_Linkage_ghost() -> u64 {
    let mut v___x_2274_: u64 = 0;
    v___x_2274_ = 13u64;
    return v___x_2274_;
}
pub unsafe fn _init_l_LLVM_Linkage_common() -> u64 {
    let mut v___x_2275_: u64 = 0;
    v___x_2275_ = 14u64;
    return v___x_2275_;
}
pub unsafe fn _init_l_LLVM_Linkage_linkerPrivate() -> u64 {
    let mut v___x_2276_: u64 = 0;
    v___x_2276_ = 15u64;
    return v___x_2276_;
}
pub unsafe fn _init_l_LLVM_Linkage_linkerPrivateWeak() -> u64 {
    let mut v___x_2277_: u64 = 0;
    v___x_2277_ = 16u64;
    return v___x_2277_;
}
pub unsafe fn l_LLVM_setLinkage___boxed(
    mut v_ctx_2282_: *mut LeanObject,
    mut v_value_2283_: *mut LeanObject,
    mut v_linkage_2284_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_2285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2286_: usize = 0;
    let mut v_value_boxed_2287_: usize = 0;
    let mut v_linkage_boxed_2288_: u64 = 0;
    let mut v_res_2289_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2286_ = lean_unbox_usize(v_ctx_2282_);
    lean_dec(v_ctx_2282_);
    v_value_boxed_2287_ = lean_unbox_usize(v_value_2283_);
    lean_dec(v_value_2283_);
    v_linkage_boxed_2288_ = lean_unbox_uint64(v_linkage_2284_);
    lean_dec_ref(v_linkage_2284_);
    v_res_2289_ = lean_llvm_set_linkage(
        v_ctx_boxed_2286_,
        v_value_boxed_2287_,
        v_linkage_boxed_2288_,
    );
    return v_res_2289_;
}
pub unsafe fn l_LLVM_i1Type(mut v_ctx_2290_: usize) -> usize {
    let mut v___x_2292_: u64 = 0;
    let mut v___x_2293_: usize = 0;
    v___x_2292_ = 1u64;
    v___x_2293_ = lean_llvm_int_type_in_context(v_ctx_2290_, v___x_2292_);
    return v___x_2293_;
}
pub unsafe fn l_LLVM_i1Type___boxed(
    mut v_ctx_2294_: *mut LeanObject,
    mut v_a_2295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2296_: usize = 0;
    let mut v_res_2297_: usize = 0;
    let mut v_r_2298_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2296_ = lean_unbox_usize(v_ctx_2294_);
    lean_dec(v_ctx_2294_);
    v_res_2297_ = l_LLVM_i1Type(v_ctx_boxed_2296_);
    v_r_2298_ = lean_box_usize(v_res_2297_);
    return v_r_2298_;
}
pub unsafe fn l_LLVM_i8Type(mut v_ctx_2299_: usize) -> usize {
    let mut v___x_2301_: u64 = 0;
    let mut v___x_2302_: usize = 0;
    v___x_2301_ = 8u64;
    v___x_2302_ = lean_llvm_int_type_in_context(v_ctx_2299_, v___x_2301_);
    return v___x_2302_;
}
pub unsafe fn l_LLVM_i8Type___boxed(
    mut v_ctx_2303_: *mut LeanObject,
    mut v_a_2304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2305_: usize = 0;
    let mut v_res_2306_: usize = 0;
    let mut v_r_2307_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2305_ = lean_unbox_usize(v_ctx_2303_);
    lean_dec(v_ctx_2303_);
    v_res_2306_ = l_LLVM_i8Type(v_ctx_boxed_2305_);
    v_r_2307_ = lean_box_usize(v_res_2306_);
    return v_r_2307_;
}
pub unsafe fn l_LLVM_i16Type(mut v_ctx_2308_: usize) -> usize {
    let mut v___x_2310_: u64 = 0;
    let mut v___x_2311_: usize = 0;
    v___x_2310_ = 16u64;
    v___x_2311_ = lean_llvm_int_type_in_context(v_ctx_2308_, v___x_2310_);
    return v___x_2311_;
}
pub unsafe fn l_LLVM_i16Type___boxed(
    mut v_ctx_2312_: *mut LeanObject,
    mut v_a_2313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2314_: usize = 0;
    let mut v_res_2315_: usize = 0;
    let mut v_r_2316_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2314_ = lean_unbox_usize(v_ctx_2312_);
    lean_dec(v_ctx_2312_);
    v_res_2315_ = l_LLVM_i16Type(v_ctx_boxed_2314_);
    v_r_2316_ = lean_box_usize(v_res_2315_);
    return v_r_2316_;
}
pub unsafe fn l_LLVM_i32Type(mut v_ctx_2317_: usize) -> usize {
    let mut v___x_2319_: u64 = 0;
    let mut v___x_2320_: usize = 0;
    v___x_2319_ = 32u64;
    v___x_2320_ = lean_llvm_int_type_in_context(v_ctx_2317_, v___x_2319_);
    return v___x_2320_;
}
pub unsafe fn l_LLVM_i32Type___boxed(
    mut v_ctx_2321_: *mut LeanObject,
    mut v_a_2322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2323_: usize = 0;
    let mut v_res_2324_: usize = 0;
    let mut v_r_2325_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2323_ = lean_unbox_usize(v_ctx_2321_);
    lean_dec(v_ctx_2321_);
    v_res_2324_ = l_LLVM_i32Type(v_ctx_boxed_2323_);
    v_r_2325_ = lean_box_usize(v_res_2324_);
    return v_r_2325_;
}
pub unsafe fn l_LLVM_i64Type(mut v_ctx_2326_: usize) -> usize {
    let mut v___x_2328_: u64 = 0;
    let mut v___x_2329_: usize = 0;
    v___x_2328_ = 64u64;
    v___x_2329_ = lean_llvm_int_type_in_context(v_ctx_2326_, v___x_2328_);
    return v___x_2329_;
}
pub unsafe fn l_LLVM_i64Type___boxed(
    mut v_ctx_2330_: *mut LeanObject,
    mut v_a_2331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2332_: usize = 0;
    let mut v_res_2333_: usize = 0;
    let mut v_r_2334_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2332_ = lean_unbox_usize(v_ctx_2330_);
    lean_dec(v_ctx_2330_);
    v_res_2333_ = l_LLVM_i64Type(v_ctx_boxed_2332_);
    v_r_2334_ = lean_box_usize(v_res_2333_);
    return v_r_2334_;
}
pub unsafe fn l_LLVM_voidPtrType(mut v_ctx_2335_: usize) -> usize {
    let mut v___x_2337_: u64 = 0;
    let mut v___x_2338_: usize = 0;
    let mut v___x_2339_: usize = 0;
    v___x_2337_ = 8u64;
    v___x_2338_ = lean_llvm_int_type_in_context(v_ctx_2335_, v___x_2337_);
    v___x_2339_ = lean_llvm_pointer_type(v_ctx_2335_, v___x_2338_);
    return v___x_2339_;
}
pub unsafe fn l_LLVM_voidPtrType___boxed(
    mut v_ctx_2340_: *mut LeanObject,
    mut v_a_2341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2342_: usize = 0;
    let mut v_res_2343_: usize = 0;
    let mut v_r_2344_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2342_ = lean_unbox_usize(v_ctx_2340_);
    lean_dec(v_ctx_2340_);
    v_res_2343_ = l_LLVM_voidPtrType(v_ctx_boxed_2342_);
    v_r_2344_ = lean_box_usize(v_res_2343_);
    return v_r_2344_;
}
pub unsafe fn l_LLVM_i8PtrType(mut v_ctx_2345_: usize) -> usize {
    let mut v___x_2347_: usize = 0;
    v___x_2347_ = l_LLVM_voidPtrType(v_ctx_2345_);
    return v___x_2347_;
}
pub unsafe fn l_LLVM_i8PtrType___boxed(
    mut v_ctx_2348_: *mut LeanObject,
    mut v_a_2349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2350_: usize = 0;
    let mut v_res_2351_: usize = 0;
    let mut v_r_2352_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2350_ = lean_unbox_usize(v_ctx_2348_);
    lean_dec(v_ctx_2348_);
    v_res_2351_ = l_LLVM_i8PtrType(v_ctx_boxed_2350_);
    v_r_2352_ = lean_box_usize(v_res_2351_);
    return v_r_2352_;
}
pub unsafe fn l_LLVM_constTrue(mut v_ctx_2353_: usize) -> usize {
    let mut v___x_2355_: usize = 0;
    let mut v___x_2356_: u64 = 0;
    let mut v___x_2357_: u8 = 0;
    let mut v___x_2358_: usize = 0;
    v___x_2355_ = l_LLVM_i1Type(v_ctx_2353_);
    v___x_2356_ = 1u64;
    v___x_2357_ = 0;
    v___x_2358_ = lean_llvm_const_int(v_ctx_2353_, v___x_2355_, v___x_2356_, v___x_2357_);
    return v___x_2358_;
}
pub unsafe fn l_LLVM_constTrue___boxed(
    mut v_ctx_2359_: *mut LeanObject,
    mut v_a_2360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2361_: usize = 0;
    let mut v_res_2362_: usize = 0;
    let mut v_r_2363_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2361_ = lean_unbox_usize(v_ctx_2359_);
    lean_dec(v_ctx_2359_);
    v_res_2362_ = l_LLVM_constTrue(v_ctx_boxed_2361_);
    v_r_2363_ = lean_box_usize(v_res_2362_);
    return v_r_2363_;
}
pub unsafe fn l_LLVM_constFalse(mut v_ctx_2364_: usize) -> usize {
    let mut v___x_2366_: usize = 0;
    let mut v___x_2367_: u64 = 0;
    let mut v___x_2368_: u8 = 0;
    let mut v___x_2369_: usize = 0;
    v___x_2366_ = l_LLVM_i1Type(v_ctx_2364_);
    v___x_2367_ = 0u64;
    v___x_2368_ = 0;
    v___x_2369_ = lean_llvm_const_int(v_ctx_2364_, v___x_2366_, v___x_2367_, v___x_2368_);
    return v___x_2369_;
}
pub unsafe fn l_LLVM_constFalse___boxed(
    mut v_ctx_2370_: *mut LeanObject,
    mut v_a_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2372_: usize = 0;
    let mut v_res_2373_: usize = 0;
    let mut v_r_2374_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2372_ = lean_unbox_usize(v_ctx_2370_);
    lean_dec(v_ctx_2370_);
    v_res_2373_ = l_LLVM_constFalse(v_ctx_boxed_2372_);
    v_r_2374_ = lean_box_usize(v_res_2373_);
    return v_r_2374_;
}
pub unsafe fn l_LLVM_constInt_x27(
    mut v_ctx_2375_: usize,
    mut v_width_2376_: u64,
    mut v_value_2377_: u64,
    mut v_signExtend_2378_: u8,
) -> usize {
    let mut v___x_2380_: usize = 0;
    let mut v___x_2381_: usize = 0;
    v___x_2380_ = lean_llvm_int_type_in_context(v_ctx_2375_, v_width_2376_);
    v___x_2381_ = lean_llvm_const_int(v_ctx_2375_, v___x_2380_, v_value_2377_, v_signExtend_2378_);
    return v___x_2381_;
}
pub unsafe fn l_LLVM_constInt_x27___boxed(
    mut v_ctx_2382_: *mut LeanObject,
    mut v_width_2383_: *mut LeanObject,
    mut v_value_2384_: *mut LeanObject,
    mut v_signExtend_2385_: *mut LeanObject,
    mut v_a_2386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2387_: usize = 0;
    let mut v_width_boxed_2388_: u64 = 0;
    let mut v_value_boxed_2389_: u64 = 0;
    let mut v_signExtend_boxed_2390_: u8 = 0;
    let mut v_res_2391_: usize = 0;
    let mut v_r_2392_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2387_ = lean_unbox_usize(v_ctx_2382_);
    lean_dec(v_ctx_2382_);
    v_width_boxed_2388_ = lean_unbox_uint64(v_width_2383_);
    lean_dec_ref(v_width_2383_);
    v_value_boxed_2389_ = lean_unbox_uint64(v_value_2384_);
    lean_dec_ref(v_value_2384_);
    v_signExtend_boxed_2390_ = (lean_unbox(v_signExtend_2385_) as u8);
    v_res_2391_ = l_LLVM_constInt_x27(
        v_ctx_boxed_2387_,
        v_width_boxed_2388_,
        v_value_boxed_2389_,
        v_signExtend_boxed_2390_,
    );
    v_r_2392_ = lean_box_usize(v_res_2391_);
    return v_r_2392_;
}
pub unsafe fn l_LLVM_constInt1(
    mut v_ctx_2393_: usize,
    mut v_value_2394_: u64,
    mut v_signExtend_2395_: u8,
) -> usize {
    let mut v___x_2397_: u64 = 0;
    let mut v___x_2398_: usize = 0;
    v___x_2397_ = 1u64;
    v___x_2398_ = l_LLVM_constInt_x27(v_ctx_2393_, v___x_2397_, v_value_2394_, v_signExtend_2395_);
    return v___x_2398_;
}
pub unsafe fn l_LLVM_constInt1___boxed(
    mut v_ctx_2399_: *mut LeanObject,
    mut v_value_2400_: *mut LeanObject,
    mut v_signExtend_2401_: *mut LeanObject,
    mut v_a_2402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2403_: usize = 0;
    let mut v_value_boxed_2404_: u64 = 0;
    let mut v_signExtend_boxed_2405_: u8 = 0;
    let mut v_res_2406_: usize = 0;
    let mut v_r_2407_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2403_ = lean_unbox_usize(v_ctx_2399_);
    lean_dec(v_ctx_2399_);
    v_value_boxed_2404_ = lean_unbox_uint64(v_value_2400_);
    lean_dec_ref(v_value_2400_);
    v_signExtend_boxed_2405_ = (lean_unbox(v_signExtend_2401_) as u8);
    v_res_2406_ = l_LLVM_constInt1(
        v_ctx_boxed_2403_,
        v_value_boxed_2404_,
        v_signExtend_boxed_2405_,
    );
    v_r_2407_ = lean_box_usize(v_res_2406_);
    return v_r_2407_;
}
pub unsafe fn l_LLVM_constInt8(
    mut v_ctx_2408_: usize,
    mut v_value_2409_: u64,
    mut v_signExtend_2410_: u8,
) -> usize {
    let mut v___x_2412_: u64 = 0;
    let mut v___x_2413_: usize = 0;
    v___x_2412_ = 8u64;
    v___x_2413_ = l_LLVM_constInt_x27(v_ctx_2408_, v___x_2412_, v_value_2409_, v_signExtend_2410_);
    return v___x_2413_;
}
pub unsafe fn l_LLVM_constInt8___boxed(
    mut v_ctx_2414_: *mut LeanObject,
    mut v_value_2415_: *mut LeanObject,
    mut v_signExtend_2416_: *mut LeanObject,
    mut v_a_2417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2418_: usize = 0;
    let mut v_value_boxed_2419_: u64 = 0;
    let mut v_signExtend_boxed_2420_: u8 = 0;
    let mut v_res_2421_: usize = 0;
    let mut v_r_2422_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2418_ = lean_unbox_usize(v_ctx_2414_);
    lean_dec(v_ctx_2414_);
    v_value_boxed_2419_ = lean_unbox_uint64(v_value_2415_);
    lean_dec_ref(v_value_2415_);
    v_signExtend_boxed_2420_ = (lean_unbox(v_signExtend_2416_) as u8);
    v_res_2421_ = l_LLVM_constInt8(
        v_ctx_boxed_2418_,
        v_value_boxed_2419_,
        v_signExtend_boxed_2420_,
    );
    v_r_2422_ = lean_box_usize(v_res_2421_);
    return v_r_2422_;
}
pub unsafe fn l_LLVM_constInt32(
    mut v_ctx_2423_: usize,
    mut v_value_2424_: u64,
    mut v_signExtend_2425_: u8,
) -> usize {
    let mut v___x_2427_: u64 = 0;
    let mut v___x_2428_: usize = 0;
    v___x_2427_ = 32u64;
    v___x_2428_ = l_LLVM_constInt_x27(v_ctx_2423_, v___x_2427_, v_value_2424_, v_signExtend_2425_);
    return v___x_2428_;
}
pub unsafe fn l_LLVM_constInt32___boxed(
    mut v_ctx_2429_: *mut LeanObject,
    mut v_value_2430_: *mut LeanObject,
    mut v_signExtend_2431_: *mut LeanObject,
    mut v_a_2432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2433_: usize = 0;
    let mut v_value_boxed_2434_: u64 = 0;
    let mut v_signExtend_boxed_2435_: u8 = 0;
    let mut v_res_2436_: usize = 0;
    let mut v_r_2437_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2433_ = lean_unbox_usize(v_ctx_2429_);
    lean_dec(v_ctx_2429_);
    v_value_boxed_2434_ = lean_unbox_uint64(v_value_2430_);
    lean_dec_ref(v_value_2430_);
    v_signExtend_boxed_2435_ = (lean_unbox(v_signExtend_2431_) as u8);
    v_res_2436_ = l_LLVM_constInt32(
        v_ctx_boxed_2433_,
        v_value_boxed_2434_,
        v_signExtend_boxed_2435_,
    );
    v_r_2437_ = lean_box_usize(v_res_2436_);
    return v_r_2437_;
}
pub unsafe fn l_LLVM_constInt64(
    mut v_ctx_2438_: usize,
    mut v_value_2439_: u64,
    mut v_signExtend_2440_: u8,
) -> usize {
    let mut v___x_2442_: u64 = 0;
    let mut v___x_2443_: usize = 0;
    v___x_2442_ = 64u64;
    v___x_2443_ = l_LLVM_constInt_x27(v_ctx_2438_, v___x_2442_, v_value_2439_, v_signExtend_2440_);
    return v___x_2443_;
}
pub unsafe fn l_LLVM_constInt64___boxed(
    mut v_ctx_2444_: *mut LeanObject,
    mut v_value_2445_: *mut LeanObject,
    mut v_signExtend_2446_: *mut LeanObject,
    mut v_a_2447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2448_: usize = 0;
    let mut v_value_boxed_2449_: u64 = 0;
    let mut v_signExtend_boxed_2450_: u8 = 0;
    let mut v_res_2451_: usize = 0;
    let mut v_r_2452_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2448_ = lean_unbox_usize(v_ctx_2444_);
    lean_dec(v_ctx_2444_);
    v_value_boxed_2449_ = lean_unbox_uint64(v_value_2445_);
    lean_dec_ref(v_value_2445_);
    v_signExtend_boxed_2450_ = (lean_unbox(v_signExtend_2446_) as u8);
    v_res_2451_ = l_LLVM_constInt64(
        v_ctx_boxed_2448_,
        v_value_boxed_2449_,
        v_signExtend_boxed_2450_,
    );
    v_r_2452_ = lean_box_usize(v_res_2451_);
    return v_r_2452_;
}
pub unsafe fn l_LLVM_constIntSizeT(
    mut v_ctx_2453_: usize,
    mut v_value_2454_: u64,
    mut v_signExtend_2455_: u8,
) -> usize {
    let mut v___x_2457_: u64 = 0;
    let mut v___x_2458_: usize = 0;
    v___x_2457_ = 64u64;
    v___x_2458_ = l_LLVM_constInt_x27(v_ctx_2453_, v___x_2457_, v_value_2454_, v_signExtend_2455_);
    return v___x_2458_;
}
pub unsafe fn l_LLVM_constIntSizeT___boxed(
    mut v_ctx_2459_: *mut LeanObject,
    mut v_value_2460_: *mut LeanObject,
    mut v_signExtend_2461_: *mut LeanObject,
    mut v_a_2462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2463_: usize = 0;
    let mut v_value_boxed_2464_: u64 = 0;
    let mut v_signExtend_boxed_2465_: u8 = 0;
    let mut v_res_2466_: usize = 0;
    let mut v_r_2467_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2463_ = lean_unbox_usize(v_ctx_2459_);
    lean_dec(v_ctx_2459_);
    v_value_boxed_2464_ = lean_unbox_uint64(v_value_2460_);
    lean_dec_ref(v_value_2460_);
    v_signExtend_boxed_2465_ = (lean_unbox(v_signExtend_2461_) as u8);
    v_res_2466_ = l_LLVM_constIntSizeT(
        v_ctx_boxed_2463_,
        v_value_boxed_2464_,
        v_signExtend_boxed_2465_,
    );
    v_r_2467_ = lean_box_usize(v_res_2466_);
    return v_r_2467_;
}
pub unsafe fn l_LLVM_constIntUnsigned(
    mut v_ctx_2468_: usize,
    mut v_value_2469_: u64,
    mut v_signExtend_2470_: u8,
) -> usize {
    let mut v___x_2472_: u64 = 0;
    let mut v___x_2473_: usize = 0;
    v___x_2472_ = 32u64;
    v___x_2473_ = l_LLVM_constInt_x27(v_ctx_2468_, v___x_2472_, v_value_2469_, v_signExtend_2470_);
    return v___x_2473_;
}
pub unsafe fn l_LLVM_constIntUnsigned___boxed(
    mut v_ctx_2474_: *mut LeanObject,
    mut v_value_2475_: *mut LeanObject,
    mut v_signExtend_2476_: *mut LeanObject,
    mut v_a_2477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_boxed_2478_: usize = 0;
    let mut v_value_boxed_2479_: u64 = 0;
    let mut v_signExtend_boxed_2480_: u8 = 0;
    let mut v_res_2481_: usize = 0;
    let mut v_r_2482_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2478_ = lean_unbox_usize(v_ctx_2474_);
    lean_dec(v_ctx_2474_);
    v_value_boxed_2479_ = lean_unbox_uint64(v_value_2475_);
    lean_dec_ref(v_value_2475_);
    v_signExtend_boxed_2480_ = (lean_unbox(v_signExtend_2476_) as u8);
    v_res_2481_ = l_LLVM_constIntUnsigned(
        v_ctx_boxed_2478_,
        v_value_boxed_2479_,
        v_signExtend_boxed_2480_,
    );
    v_r_2482_ = lean_box_usize(v_res_2481_);
    return v_r_2482_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_LLVMBindings(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_LLVM_CodegenFileType_AssemblyFile = _init_l_LLVM_CodegenFileType_AssemblyFile();
    l_LLVM_CodegenFileType_ObjectFile = _init_l_LLVM_CodegenFileType_ObjectFile();
    l_LLVM_IntPredicate_EQ = _init_l_LLVM_IntPredicate_EQ();
    l_LLVM_IntPredicate_NE = _init_l_LLVM_IntPredicate_NE();
    l_LLVM_IntPredicate_UGT = _init_l_LLVM_IntPredicate_UGT();
    l_LLVM_AttributeIndex_AttributeReturnIndex = _init_l_LLVM_AttributeIndex_AttributeReturnIndex();
    l_LLVM_AttributeIndex_AttributeFunctionIndex =
        _init_l_LLVM_AttributeIndex_AttributeFunctionIndex();
    l_LLVM_Visibility_default = _init_l_LLVM_Visibility_default();
    l_LLVM_Visibility_hidden = _init_l_LLVM_Visibility_hidden();
    l_LLVM_Visibility_protected = _init_l_LLVM_Visibility_protected();
    l_LLVM_DLLStorageClass_default = _init_l_LLVM_DLLStorageClass_default();
    l_LLVM_DLLStorageClass_import = _init_l_LLVM_DLLStorageClass_import();
    l_LLVM_DLLStorageClass_export = _init_l_LLVM_DLLStorageClass_export();
    l_LLVM_Linkage_external = _init_l_LLVM_Linkage_external();
    l_LLVM_Linkage_availableExternally = _init_l_LLVM_Linkage_availableExternally();
    l_LLVM_Linkage_linkOnceAny = _init_l_LLVM_Linkage_linkOnceAny();
    l_LLVM_Linkage_linkOnceODR = _init_l_LLVM_Linkage_linkOnceODR();
    l_LLVM_Linkage_linkOnceODRAutoHide = _init_l_LLVM_Linkage_linkOnceODRAutoHide();
    l_LLVM_Linkage_weakAny = _init_l_LLVM_Linkage_weakAny();
    l_LLVM_Linkage_weakODR = _init_l_LLVM_Linkage_weakODR();
    l_LLVM_Linkage_appending = _init_l_LLVM_Linkage_appending();
    l_LLVM_Linkage_internal = _init_l_LLVM_Linkage_internal();
    l_LLVM_Linkage_private = _init_l_LLVM_Linkage_private();
    l_LLVM_Linkage_dllImport = _init_l_LLVM_Linkage_dllImport();
    l_LLVM_Linkage_dllExport = _init_l_LLVM_Linkage_dllExport();
    l_LLVM_Linkage_externalWeak = _init_l_LLVM_Linkage_externalWeak();
    l_LLVM_Linkage_ghost = _init_l_LLVM_Linkage_ghost();
    l_LLVM_Linkage_common = _init_l_LLVM_Linkage_common();
    l_LLVM_Linkage_linkerPrivate = _init_l_LLVM_Linkage_linkerPrivate();
    l_LLVM_Linkage_linkerPrivateWeak = _init_l_LLVM_Linkage_linkerPrivateWeak();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_LLVMBindings(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_IR_LLVMBindings(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_LLVMBindings(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_LLVMBindings(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_LLVMBindings(builtin);
}
