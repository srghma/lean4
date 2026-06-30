// Lean compiler output
// Module: Lean.Compiler.IR.LLVMBindings
// Imports: Init.System.IO
use crate::ffi::{
    lean_llvm_add_attribute_at_index, lean_llvm_add_case, lean_llvm_add_function,
    lean_llvm_add_global, lean_llvm_append_basic_block_in_context, lean_llvm_array_type,
    lean_llvm_build_add, lean_llvm_build_alloca, lean_llvm_build_br, lean_llvm_build_call2,
    lean_llvm_build_cond_br, lean_llvm_build_gep2, lean_llvm_build_global_string,
    lean_llvm_build_icmp, lean_llvm_build_inbounds_gep2, lean_llvm_build_load2,
    lean_llvm_build_mul, lean_llvm_build_not, lean_llvm_build_ptr_to_int, lean_llvm_build_ret,
    lean_llvm_build_sext, lean_llvm_build_sext_or_trunc, lean_llvm_build_store,
    lean_llvm_build_sub, lean_llvm_build_switch, lean_llvm_build_unreachable, lean_llvm_build_zext,
    lean_llvm_clear_insertion_position, lean_llvm_const_array, lean_llvm_const_int,
    lean_llvm_const_pointer_null, lean_llvm_const_string, lean_llvm_count_basic_blocks,
    lean_llvm_create_builder_in_context, lean_llvm_create_context,
    lean_llvm_create_memory_buffer_with_contents_of_file, lean_llvm_create_module,
    lean_llvm_create_string_attribute, lean_llvm_create_target_machine, lean_llvm_dispose_module,
    lean_llvm_dispose_target_machine, lean_llvm_double_type_in_context,
    lean_llvm_float_type_in_context, lean_llvm_function_type, lean_llvm_get_basic_block_parent,
    lean_llvm_get_default_target_triple, lean_llvm_get_entry_basic_block,
    lean_llvm_get_first_function, lean_llvm_get_first_global, lean_llvm_get_first_instruction,
    lean_llvm_get_insert_block, lean_llvm_get_named_function, lean_llvm_get_named_global,
    lean_llvm_get_next_function, lean_llvm_get_next_global, lean_llvm_get_target_from_triple,
    lean_llvm_get_undef, lean_llvm_get_value_name2, lean_llvm_initialize_target_info,
    lean_llvm_int_type_in_context, lean_llvm_link_modules, lean_llvm_module_to_string,
    lean_llvm_opaque_pointer_type_in_context, lean_llvm_parse_bitcode, lean_llvm_pointer_type,
    lean_llvm_position_builder_at_end, lean_llvm_position_builder_before,
    lean_llvm_print_module_to_file, lean_llvm_print_module_to_string,
    lean_llvm_set_dll_storage_class, lean_llvm_set_initializer, lean_llvm_set_linkage,
    lean_llvm_set_tail_call, lean_llvm_set_visibility, lean_llvm_target_machine_emit_to_file,
    lean_llvm_type_of, lean_llvm_verify_module, lean_llvm_void_type_in_context,
    lean_llvm_write_bitcode_to_file, lean_usize_dec_eq, llvm_count_params, llvm_get_param,
    llvm_is_declaration,
};
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
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
    mut v_v_1252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_1253_: usize = 0;
    let mut v_res_1254_: u8 = 0;
    let mut v_r_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_1253_ = leanh::lean_unbox_usize(v_v_1252_);
    leanh::lean_dec(v_v_1252_);
    v_res_1254_ = l_LLVM_Value_isNull___redArg(v_v_boxed_1253_);
    v_r_1255_ = leanh::lean_box((v_res_1254_) as usize);
    return v_r_1255_;
}
pub unsafe fn l_LLVM_Value_isNull(mut v_ctx_1256_: usize, mut v_v_1257_: usize) -> u8 {
    let mut v___x_1258_: u8 = 0;
    v___x_1258_ = l_LLVM_Value_isNull___redArg(v_v_1257_);
    return v___x_1258_;
}
pub unsafe fn l_LLVM_Value_isNull___boxed(
    mut v_ctx_1259_: *mut leanh::LeanObject,
    mut v_v_1260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1261_: usize = 0;
    let mut v_v_boxed_1262_: usize = 0;
    let mut v_res_1263_: u8 = 0;
    let mut v_r_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1261_ = leanh::lean_unbox_usize(v_ctx_1259_);
    leanh::lean_dec(v_ctx_1259_);
    v_v_boxed_1262_ = leanh::lean_unbox_usize(v_v_1260_);
    leanh::lean_dec(v_v_1260_);
    v_res_1263_ = l_LLVM_Value_isNull(v_ctx_boxed_1261_, v_v_boxed_1262_);
    v_r_1264_ = leanh::lean_box((v_res_1263_) as usize);
    return v_r_1264_;
}
pub unsafe fn l_LLVM_Value_getName___boxed(
    mut v_ctx_1268_: *mut leanh::LeanObject,
    mut v_value_1269_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1271_: usize = 0;
    let mut v_value_boxed_1272_: usize = 0;
    let mut v_res_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1271_ = leanh::lean_unbox_usize(v_ctx_1268_);
    leanh::lean_dec(v_ctx_1268_);
    v_value_boxed_1272_ = leanh::lean_unbox_usize(v_value_1269_);
    leanh::lean_dec(v_value_1269_);
    v_res_1273_ = lean_llvm_get_value_name2(v_ctx_boxed_1271_, v_value_boxed_1272_);
    return v_res_1273_;
}
pub unsafe fn l_LLVM_llvmInitializeTargetInfo___boxed(
    mut v_a_00___x40___internal___hyg_1275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1276_ = lean_llvm_initialize_target_info();
    return v_res_1276_;
}
pub unsafe fn l_LLVM_createContext___boxed(
    mut v_a_00___x40___internal___hyg_1278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1279_: usize = 0;
    let mut v_r_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1279_ = lean_llvm_create_context();
    v_r_1280_ = leanh::lean_box_usize(v_res_1279_);
    return v_r_1280_;
}
pub unsafe fn l_LLVM_createModule___boxed(
    mut v_ctx_1284_: *mut leanh::LeanObject,
    mut v_name_1285_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1287_: usize = 0;
    let mut v_res_1288_: usize = 0;
    let mut v_r_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1287_ = leanh::lean_unbox_usize(v_ctx_1284_);
    leanh::lean_dec(v_ctx_1284_);
    v_res_1288_ = lean_llvm_create_module(v_ctx_boxed_1287_, v_name_1285_);
    leanh::lean_dec_ref(v_name_1285_);
    v_r_1289_ = leanh::lean_box_usize(v_res_1288_);
    return v_r_1289_;
}
pub unsafe fn l_LLVM_moduleToString___boxed(
    mut v_ctx_1293_: *mut leanh::LeanObject,
    mut v_m_1294_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1296_: usize = 0;
    let mut v_m_boxed_1297_: usize = 0;
    let mut v_res_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1296_ = leanh::lean_unbox_usize(v_ctx_1293_);
    leanh::lean_dec(v_ctx_1293_);
    v_m_boxed_1297_ = leanh::lean_unbox_usize(v_m_1294_);
    leanh::lean_dec(v_m_1294_);
    v_res_1298_ = lean_llvm_module_to_string(v_ctx_boxed_1296_, v_m_boxed_1297_);
    return v_res_1298_;
}
pub unsafe fn l_LLVM_writeBitcodeToFile___boxed(
    mut v_ctx_1303_: *mut leanh::LeanObject,
    mut v_m_1304_: *mut leanh::LeanObject,
    mut v_path_1305_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1307_: usize = 0;
    let mut v_m_boxed_1308_: usize = 0;
    let mut v_res_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1307_ = leanh::lean_unbox_usize(v_ctx_1303_);
    leanh::lean_dec(v_ctx_1303_);
    v_m_boxed_1308_ = leanh::lean_unbox_usize(v_m_1304_);
    leanh::lean_dec(v_m_1304_);
    v_res_1309_ = lean_llvm_write_bitcode_to_file(v_ctx_boxed_1307_, v_m_boxed_1308_, v_path_1305_);
    leanh::lean_dec_ref(v_path_1305_);
    return v_res_1309_;
}
pub unsafe fn l_LLVM_addFunction___boxed(
    mut v_ctx_1315_: *mut leanh::LeanObject,
    mut v_m_1316_: *mut leanh::LeanObject,
    mut v_name_1317_: *mut leanh::LeanObject,
    mut v_type_1318_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1320_: usize = 0;
    let mut v_m_boxed_1321_: usize = 0;
    let mut v_type_boxed_1322_: usize = 0;
    let mut v_res_1323_: usize = 0;
    let mut v_r_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1320_ = leanh::lean_unbox_usize(v_ctx_1315_);
    leanh::lean_dec(v_ctx_1315_);
    v_m_boxed_1321_ = leanh::lean_unbox_usize(v_m_1316_);
    leanh::lean_dec(v_m_1316_);
    v_type_boxed_1322_ = leanh::lean_unbox_usize(v_type_1318_);
    leanh::lean_dec(v_type_1318_);
    v_res_1323_ = lean_llvm_add_function(
        v_ctx_boxed_1320_,
        v_m_boxed_1321_,
        v_name_1317_,
        v_type_boxed_1322_,
    );
    leanh::lean_dec_ref(v_name_1317_);
    v_r_1324_ = leanh::lean_box_usize(v_res_1323_);
    return v_r_1324_;
}
pub unsafe fn l_LLVM_getFirstFunction___boxed(
    mut v_ctx_1328_: *mut leanh::LeanObject,
    mut v_m_1329_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1331_: usize = 0;
    let mut v_m_boxed_1332_: usize = 0;
    let mut v_res_1333_: usize = 0;
    let mut v_r_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1331_ = leanh::lean_unbox_usize(v_ctx_1328_);
    leanh::lean_dec(v_ctx_1328_);
    v_m_boxed_1332_ = leanh::lean_unbox_usize(v_m_1329_);
    leanh::lean_dec(v_m_1329_);
    v_res_1333_ = lean_llvm_get_first_function(v_ctx_boxed_1331_, v_m_boxed_1332_);
    v_r_1334_ = leanh::lean_box_usize(v_res_1333_);
    return v_r_1334_;
}
pub unsafe fn l_LLVM_getNextFunction___boxed(
    mut v_ctx_1338_: *mut leanh::LeanObject,
    mut v_glbl_1339_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1341_: usize = 0;
    let mut v_glbl_boxed_1342_: usize = 0;
    let mut v_res_1343_: usize = 0;
    let mut v_r_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1341_ = leanh::lean_unbox_usize(v_ctx_1338_);
    leanh::lean_dec(v_ctx_1338_);
    v_glbl_boxed_1342_ = leanh::lean_unbox_usize(v_glbl_1339_);
    leanh::lean_dec(v_glbl_1339_);
    v_res_1343_ = lean_llvm_get_next_function(v_ctx_boxed_1341_, v_glbl_boxed_1342_);
    v_r_1344_ = leanh::lean_box_usize(v_res_1343_);
    return v_r_1344_;
}
pub unsafe fn l_LLVM_getNamedFunction___boxed(
    mut v_ctx_1349_: *mut leanh::LeanObject,
    mut v_m_1350_: *mut leanh::LeanObject,
    mut v_name_1351_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1353_: usize = 0;
    let mut v_m_boxed_1354_: usize = 0;
    let mut v_res_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1353_ = leanh::lean_unbox_usize(v_ctx_1349_);
    leanh::lean_dec(v_ctx_1349_);
    v_m_boxed_1354_ = leanh::lean_unbox_usize(v_m_1350_);
    leanh::lean_dec(v_m_1350_);
    v_res_1355_ = lean_llvm_get_named_function(v_ctx_boxed_1353_, v_m_boxed_1354_, v_name_1351_);
    leanh::lean_dec_ref(v_name_1351_);
    return v_res_1355_;
}
pub unsafe fn l_LLVM_addGlobal___boxed(
    mut v_ctx_1361_: *mut leanh::LeanObject,
    mut v_m_1362_: *mut leanh::LeanObject,
    mut v_name_1363_: *mut leanh::LeanObject,
    mut v_type_1364_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1366_: usize = 0;
    let mut v_m_boxed_1367_: usize = 0;
    let mut v_type_boxed_1368_: usize = 0;
    let mut v_res_1369_: usize = 0;
    let mut v_r_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1366_ = leanh::lean_unbox_usize(v_ctx_1361_);
    leanh::lean_dec(v_ctx_1361_);
    v_m_boxed_1367_ = leanh::lean_unbox_usize(v_m_1362_);
    leanh::lean_dec(v_m_1362_);
    v_type_boxed_1368_ = leanh::lean_unbox_usize(v_type_1364_);
    leanh::lean_dec(v_type_1364_);
    v_res_1369_ = lean_llvm_add_global(
        v_ctx_boxed_1366_,
        v_m_boxed_1367_,
        v_name_1363_,
        v_type_boxed_1368_,
    );
    leanh::lean_dec_ref(v_name_1363_);
    v_r_1370_ = leanh::lean_box_usize(v_res_1369_);
    return v_r_1370_;
}
pub unsafe fn l_LLVM_getNamedGlobal___boxed(
    mut v_ctx_1375_: *mut leanh::LeanObject,
    mut v_m_1376_: *mut leanh::LeanObject,
    mut v_name_1377_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1379_: usize = 0;
    let mut v_m_boxed_1380_: usize = 0;
    let mut v_res_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1379_ = leanh::lean_unbox_usize(v_ctx_1375_);
    leanh::lean_dec(v_ctx_1375_);
    v_m_boxed_1380_ = leanh::lean_unbox_usize(v_m_1376_);
    leanh::lean_dec(v_m_1376_);
    v_res_1381_ = lean_llvm_get_named_global(v_ctx_boxed_1379_, v_m_boxed_1380_, v_name_1377_);
    leanh::lean_dec_ref(v_name_1377_);
    return v_res_1381_;
}
pub unsafe fn l_LLVM_getFirstGlobal___boxed(
    mut v_ctx_1385_: *mut leanh::LeanObject,
    mut v_m_1386_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1388_: usize = 0;
    let mut v_m_boxed_1389_: usize = 0;
    let mut v_res_1390_: usize = 0;
    let mut v_r_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1388_ = leanh::lean_unbox_usize(v_ctx_1385_);
    leanh::lean_dec(v_ctx_1385_);
    v_m_boxed_1389_ = leanh::lean_unbox_usize(v_m_1386_);
    leanh::lean_dec(v_m_1386_);
    v_res_1390_ = lean_llvm_get_first_global(v_ctx_boxed_1388_, v_m_boxed_1389_);
    v_r_1391_ = leanh::lean_box_usize(v_res_1390_);
    return v_r_1391_;
}
pub unsafe fn l_LLVM_getNextGlobal___boxed(
    mut v_ctx_1395_: *mut leanh::LeanObject,
    mut v_glbl_1396_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1398_: usize = 0;
    let mut v_glbl_boxed_1399_: usize = 0;
    let mut v_res_1400_: usize = 0;
    let mut v_r_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1398_ = leanh::lean_unbox_usize(v_ctx_1395_);
    leanh::lean_dec(v_ctx_1395_);
    v_glbl_boxed_1399_ = leanh::lean_unbox_usize(v_glbl_1396_);
    leanh::lean_dec(v_glbl_1396_);
    v_res_1400_ = lean_llvm_get_next_global(v_ctx_boxed_1398_, v_glbl_boxed_1399_);
    v_r_1401_ = leanh::lean_box_usize(v_res_1400_);
    return v_r_1401_;
}
pub unsafe fn l_LLVM_buildGlobalString___boxed(
    mut v_ctx_1407_: *mut leanh::LeanObject,
    mut v_builder_1408_: *mut leanh::LeanObject,
    mut v_value_1409_: *mut leanh::LeanObject,
    mut v_name_1410_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1412_: usize = 0;
    let mut v_builder_boxed_1413_: usize = 0;
    let mut v_res_1414_: usize = 0;
    let mut v_r_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1412_ = leanh::lean_unbox_usize(v_ctx_1407_);
    leanh::lean_dec(v_ctx_1407_);
    v_builder_boxed_1413_ = leanh::lean_unbox_usize(v_builder_1408_);
    leanh::lean_dec(v_builder_1408_);
    v_res_1414_ = lean_llvm_build_global_string(
        v_ctx_boxed_1412_,
        v_builder_boxed_1413_,
        v_value_1409_,
        v_name_1410_,
    );
    leanh::lean_dec_ref(v_value_1409_);
    v_r_1415_ = leanh::lean_box_usize(v_res_1414_);
    return v_r_1415_;
}
pub unsafe fn l_LLVM_isDeclaration___boxed(
    mut v_ctx_1419_: *mut leanh::LeanObject,
    mut v_global_1420_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1422_: usize = 0;
    let mut v_global_boxed_1423_: usize = 0;
    let mut v_res_1424_: u8 = 0;
    let mut v_r_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1422_ = leanh::lean_unbox_usize(v_ctx_1419_);
    leanh::lean_dec(v_ctx_1419_);
    v_global_boxed_1423_ = leanh::lean_unbox_usize(v_global_1420_);
    leanh::lean_dec(v_global_1420_);
    v_res_1424_ = llvm_is_declaration(v_ctx_boxed_1422_, v_global_boxed_1423_);
    v_r_1425_ = leanh::lean_box((v_res_1424_) as usize);
    return v_r_1425_;
}
pub unsafe fn l_LLVM_setInitializer___boxed(
    mut v_ctx_1430_: *mut leanh::LeanObject,
    mut v_glbl_1431_: *mut leanh::LeanObject,
    mut v_val_1432_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1434_: usize = 0;
    let mut v_glbl_boxed_1435_: usize = 0;
    let mut v_val_boxed_1436_: usize = 0;
    let mut v_res_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1434_ = leanh::lean_unbox_usize(v_ctx_1430_);
    leanh::lean_dec(v_ctx_1430_);
    v_glbl_boxed_1435_ = leanh::lean_unbox_usize(v_glbl_1431_);
    leanh::lean_dec(v_glbl_1431_);
    v_val_boxed_1436_ = leanh::lean_unbox_usize(v_val_1432_);
    leanh::lean_dec(v_val_1432_);
    v_res_1437_ =
        lean_llvm_set_initializer(v_ctx_boxed_1434_, v_glbl_boxed_1435_, v_val_boxed_1436_);
    return v_res_1437_;
}
pub unsafe fn l_LLVM_functionType___boxed(
    mut v_ctx_1443_: *mut leanh::LeanObject,
    mut v_retty_1444_: *mut leanh::LeanObject,
    mut v_args_1445_: *mut leanh::LeanObject,
    mut v_isVarArg_1446_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1448_: usize = 0;
    let mut v_retty_boxed_1449_: usize = 0;
    let mut v_isVarArg_boxed_1450_: u8 = 0;
    let mut v_res_1451_: usize = 0;
    let mut v_r_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1448_ = leanh::lean_unbox_usize(v_ctx_1443_);
    leanh::lean_dec(v_ctx_1443_);
    v_retty_boxed_1449_ = leanh::lean_unbox_usize(v_retty_1444_);
    leanh::lean_dec(v_retty_1444_);
    v_isVarArg_boxed_1450_ = (leanh::lean_unbox(v_isVarArg_1446_) as u8);
    v_res_1451_ = lean_llvm_function_type(
        v_ctx_boxed_1448_,
        v_retty_boxed_1449_,
        v_args_1445_,
        v_isVarArg_boxed_1450_,
    );
    leanh::lean_dec_ref(v_args_1445_);
    v_r_1452_ = leanh::lean_box_usize(v_res_1451_);
    return v_r_1452_;
}
pub unsafe fn l_LLVM_voidType___boxed(
    mut v_ctx_1455_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1457_: usize = 0;
    let mut v_res_1458_: usize = 0;
    let mut v_r_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1457_ = leanh::lean_unbox_usize(v_ctx_1455_);
    leanh::lean_dec(v_ctx_1455_);
    v_res_1458_ = lean_llvm_void_type_in_context(v_ctx_boxed_1457_);
    v_r_1459_ = leanh::lean_box_usize(v_res_1458_);
    return v_r_1459_;
}
pub unsafe fn l_LLVM_intTypeInContext___boxed(
    mut v_ctx_1463_: *mut leanh::LeanObject,
    mut v_width_1464_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1466_: usize = 0;
    let mut v_width_boxed_1467_: u64 = 0;
    let mut v_res_1468_: usize = 0;
    let mut v_r_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1466_ = leanh::lean_unbox_usize(v_ctx_1463_);
    leanh::lean_dec(v_ctx_1463_);
    v_width_boxed_1467_ = leanh::lean_unbox_uint64(v_width_1464_);
    leanh::lean_dec_ref(v_width_1464_);
    v_res_1468_ = lean_llvm_int_type_in_context(v_ctx_boxed_1466_, v_width_boxed_1467_);
    v_r_1469_ = leanh::lean_box_usize(v_res_1468_);
    return v_r_1469_;
}
pub unsafe fn l_LLVM_opaquePointerTypeInContext___boxed(
    mut v_ctx_1473_: *mut leanh::LeanObject,
    mut v_addrspace_1474_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1476_: usize = 0;
    let mut v_addrspace_boxed_1477_: u64 = 0;
    let mut v_res_1478_: usize = 0;
    let mut v_r_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1476_ = leanh::lean_unbox_usize(v_ctx_1473_);
    leanh::lean_dec(v_ctx_1473_);
    v_addrspace_boxed_1477_ = leanh::lean_unbox_uint64(v_addrspace_1474_);
    leanh::lean_dec_ref(v_addrspace_1474_);
    v_res_1478_ =
        lean_llvm_opaque_pointer_type_in_context(v_ctx_boxed_1476_, v_addrspace_boxed_1477_);
    v_r_1479_ = leanh::lean_box_usize(v_res_1478_);
    return v_r_1479_;
}
pub unsafe fn l_LLVM_floatTypeInContext___boxed(
    mut v_ctx_1482_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1484_: usize = 0;
    let mut v_res_1485_: usize = 0;
    let mut v_r_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1484_ = leanh::lean_unbox_usize(v_ctx_1482_);
    leanh::lean_dec(v_ctx_1482_);
    v_res_1485_ = lean_llvm_float_type_in_context(v_ctx_boxed_1484_);
    v_r_1486_ = leanh::lean_box_usize(v_res_1485_);
    return v_r_1486_;
}
pub unsafe fn l_LLVM_doubleTypeInContext___boxed(
    mut v_ctx_1489_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1491_: usize = 0;
    let mut v_res_1492_: usize = 0;
    let mut v_r_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1491_ = leanh::lean_unbox_usize(v_ctx_1489_);
    leanh::lean_dec(v_ctx_1489_);
    v_res_1492_ = lean_llvm_double_type_in_context(v_ctx_boxed_1491_);
    v_r_1493_ = leanh::lean_box_usize(v_res_1492_);
    return v_r_1493_;
}
pub unsafe fn l_LLVM_pointerType___boxed(
    mut v_ctx_1497_: *mut leanh::LeanObject,
    mut v_elemty_1498_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1500_: usize = 0;
    let mut v_elemty_boxed_1501_: usize = 0;
    let mut v_res_1502_: usize = 0;
    let mut v_r_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1500_ = leanh::lean_unbox_usize(v_ctx_1497_);
    leanh::lean_dec(v_ctx_1497_);
    v_elemty_boxed_1501_ = leanh::lean_unbox_usize(v_elemty_1498_);
    leanh::lean_dec(v_elemty_1498_);
    v_res_1502_ = lean_llvm_pointer_type(v_ctx_boxed_1500_, v_elemty_boxed_1501_);
    v_r_1503_ = leanh::lean_box_usize(v_res_1502_);
    return v_r_1503_;
}
pub unsafe fn l_LLVM_arrayType___boxed(
    mut v_ctx_1508_: *mut leanh::LeanObject,
    mut v_elemty_1509_: *mut leanh::LeanObject,
    mut v_nelem_1510_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1512_: usize = 0;
    let mut v_elemty_boxed_1513_: usize = 0;
    let mut v_nelem_boxed_1514_: u64 = 0;
    let mut v_res_1515_: usize = 0;
    let mut v_r_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1512_ = leanh::lean_unbox_usize(v_ctx_1508_);
    leanh::lean_dec(v_ctx_1508_);
    v_elemty_boxed_1513_ = leanh::lean_unbox_usize(v_elemty_1509_);
    leanh::lean_dec(v_elemty_1509_);
    v_nelem_boxed_1514_ = leanh::lean_unbox_uint64(v_nelem_1510_);
    leanh::lean_dec_ref(v_nelem_1510_);
    v_res_1515_ =
        lean_llvm_array_type(v_ctx_boxed_1512_, v_elemty_boxed_1513_, v_nelem_boxed_1514_);
    v_r_1516_ = leanh::lean_box_usize(v_res_1515_);
    return v_r_1516_;
}
pub unsafe fn l_LLVM_constArray___boxed(
    mut v_ctx_1521_: *mut leanh::LeanObject,
    mut v_elemty_1522_: *mut leanh::LeanObject,
    mut v_vals_1523_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1525_: usize = 0;
    let mut v_elemty_boxed_1526_: usize = 0;
    let mut v_res_1527_: usize = 0;
    let mut v_r_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1525_ = leanh::lean_unbox_usize(v_ctx_1521_);
    leanh::lean_dec(v_ctx_1521_);
    v_elemty_boxed_1526_ = leanh::lean_unbox_usize(v_elemty_1522_);
    leanh::lean_dec(v_elemty_1522_);
    v_res_1527_ = lean_llvm_const_array(v_ctx_boxed_1525_, v_elemty_boxed_1526_, v_vals_1523_);
    leanh::lean_dec_ref(v_vals_1523_);
    v_r_1528_ = leanh::lean_box_usize(v_res_1527_);
    return v_r_1528_;
}
pub unsafe fn l_LLVM_constString___boxed(
    mut v_ctx_1532_: *mut leanh::LeanObject,
    mut v_str_1533_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1535_: usize = 0;
    let mut v_res_1536_: usize = 0;
    let mut v_r_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1535_ = leanh::lean_unbox_usize(v_ctx_1532_);
    leanh::lean_dec(v_ctx_1532_);
    v_res_1536_ = lean_llvm_const_string(v_ctx_boxed_1535_, v_str_1533_);
    leanh::lean_dec_ref(v_str_1533_);
    v_r_1537_ = leanh::lean_box_usize(v_res_1536_);
    return v_r_1537_;
}
pub unsafe fn l_LLVM_constPointerNull___boxed(
    mut v_ctx_1541_: *mut leanh::LeanObject,
    mut v_elemty_1542_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1544_: usize = 0;
    let mut v_elemty_boxed_1545_: usize = 0;
    let mut v_res_1546_: usize = 0;
    let mut v_r_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1544_ = leanh::lean_unbox_usize(v_ctx_1541_);
    leanh::lean_dec(v_ctx_1541_);
    v_elemty_boxed_1545_ = leanh::lean_unbox_usize(v_elemty_1542_);
    leanh::lean_dec(v_elemty_1542_);
    v_res_1546_ = lean_llvm_const_pointer_null(v_ctx_boxed_1544_, v_elemty_boxed_1545_);
    v_r_1547_ = leanh::lean_box_usize(v_res_1546_);
    return v_r_1547_;
}
pub unsafe fn l_LLVM_getUndef___boxed(
    mut v_ctx_1551_: *mut leanh::LeanObject,
    mut v_elemty_1552_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1554_: usize = 0;
    let mut v_elemty_boxed_1555_: usize = 0;
    let mut v_res_1556_: usize = 0;
    let mut v_r_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1554_ = leanh::lean_unbox_usize(v_ctx_1551_);
    leanh::lean_dec(v_ctx_1551_);
    v_elemty_boxed_1555_ = leanh::lean_unbox_usize(v_elemty_1552_);
    leanh::lean_dec(v_elemty_1552_);
    v_res_1556_ = lean_llvm_get_undef(v_ctx_boxed_1554_, v_elemty_boxed_1555_);
    v_r_1557_ = leanh::lean_box_usize(v_res_1556_);
    return v_r_1557_;
}
pub unsafe fn l_LLVM_createBuilderInContext___boxed(
    mut v_ctx_1560_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1562_: usize = 0;
    let mut v_res_1563_: usize = 0;
    let mut v_r_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1562_ = leanh::lean_unbox_usize(v_ctx_1560_);
    leanh::lean_dec(v_ctx_1560_);
    v_res_1563_ = lean_llvm_create_builder_in_context(v_ctx_boxed_1562_);
    v_r_1564_ = leanh::lean_box_usize(v_res_1563_);
    return v_r_1564_;
}
pub unsafe fn l_LLVM_appendBasicBlockInContext___boxed(
    mut v_ctx_1569_: *mut leanh::LeanObject,
    mut v_fn_1570_: *mut leanh::LeanObject,
    mut v_name_1571_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1573_: usize = 0;
    let mut v_fn_boxed_1574_: usize = 0;
    let mut v_res_1575_: usize = 0;
    let mut v_r_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1573_ = leanh::lean_unbox_usize(v_ctx_1569_);
    leanh::lean_dec(v_ctx_1569_);
    v_fn_boxed_1574_ = leanh::lean_unbox_usize(v_fn_1570_);
    leanh::lean_dec(v_fn_1570_);
    v_res_1575_ =
        lean_llvm_append_basic_block_in_context(v_ctx_boxed_1573_, v_fn_boxed_1574_, v_name_1571_);
    leanh::lean_dec_ref(v_name_1571_);
    v_r_1576_ = leanh::lean_box_usize(v_res_1575_);
    return v_r_1576_;
}
pub unsafe fn l_LLVM_countBasicBlocks___boxed(
    mut v_ctx_1580_: *mut leanh::LeanObject,
    mut v_fn_1581_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1583_: usize = 0;
    let mut v_fn_boxed_1584_: usize = 0;
    let mut v_res_1585_: u64 = 0;
    let mut v_r_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1583_ = leanh::lean_unbox_usize(v_ctx_1580_);
    leanh::lean_dec(v_ctx_1580_);
    v_fn_boxed_1584_ = leanh::lean_unbox_usize(v_fn_1581_);
    leanh::lean_dec(v_fn_1581_);
    v_res_1585_ = lean_llvm_count_basic_blocks(v_ctx_boxed_1583_, v_fn_boxed_1584_);
    v_r_1586_ = leanh::lean_box_uint64(v_res_1585_);
    return v_r_1586_;
}
pub unsafe fn l_LLVM_getEntryBasicBlock___boxed(
    mut v_ctx_1590_: *mut leanh::LeanObject,
    mut v_fn_1591_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1593_: usize = 0;
    let mut v_fn_boxed_1594_: usize = 0;
    let mut v_res_1595_: usize = 0;
    let mut v_r_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1593_ = leanh::lean_unbox_usize(v_ctx_1590_);
    leanh::lean_dec(v_ctx_1590_);
    v_fn_boxed_1594_ = leanh::lean_unbox_usize(v_fn_1591_);
    leanh::lean_dec(v_fn_1591_);
    v_res_1595_ = lean_llvm_get_entry_basic_block(v_ctx_boxed_1593_, v_fn_boxed_1594_);
    v_r_1596_ = leanh::lean_box_usize(v_res_1595_);
    return v_r_1596_;
}
pub unsafe fn l_LLVM_getFirstInstruction___boxed(
    mut v_ctx_1600_: *mut leanh::LeanObject,
    mut v_bb_1601_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1603_: usize = 0;
    let mut v_bb_boxed_1604_: usize = 0;
    let mut v_res_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1603_ = leanh::lean_unbox_usize(v_ctx_1600_);
    leanh::lean_dec(v_ctx_1600_);
    v_bb_boxed_1604_ = leanh::lean_unbox_usize(v_bb_1601_);
    leanh::lean_dec(v_bb_1601_);
    v_res_1605_ = lean_llvm_get_first_instruction(v_ctx_boxed_1603_, v_bb_boxed_1604_);
    return v_res_1605_;
}
pub unsafe fn l_LLVM_positionBuilderBefore___boxed(
    mut v_ctx_1610_: *mut leanh::LeanObject,
    mut v_builder_1611_: *mut leanh::LeanObject,
    mut v_instr_1612_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1614_: usize = 0;
    let mut v_builder_boxed_1615_: usize = 0;
    let mut v_instr_boxed_1616_: usize = 0;
    let mut v_res_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1614_ = leanh::lean_unbox_usize(v_ctx_1610_);
    leanh::lean_dec(v_ctx_1610_);
    v_builder_boxed_1615_ = leanh::lean_unbox_usize(v_builder_1611_);
    leanh::lean_dec(v_builder_1611_);
    v_instr_boxed_1616_ = leanh::lean_unbox_usize(v_instr_1612_);
    leanh::lean_dec(v_instr_1612_);
    v_res_1617_ = lean_llvm_position_builder_before(
        v_ctx_boxed_1614_,
        v_builder_boxed_1615_,
        v_instr_boxed_1616_,
    );
    return v_res_1617_;
}
pub unsafe fn l_LLVM_positionBuilderAtEnd___boxed(
    mut v_Context_00___x40_Lean_Compiler_IR_LLVMBindings_2945912803____hygCtx___hyg_1623_: *mut leanh::LeanObject,
    mut v_ctx_1624_: *mut leanh::LeanObject,
    mut v_builder_1625_: *mut leanh::LeanObject,
    mut v_bb_1626_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_builder_boxed_1628_: usize = 0;
    let mut v_bb_boxed_1629_: usize = 0;
    let mut v_res_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_builder_boxed_1628_ = leanh::lean_unbox_usize(v_builder_1625_);
    leanh::lean_dec(v_builder_1625_);
    v_bb_boxed_1629_ = leanh::lean_unbox_usize(v_bb_1626_);
    leanh::lean_dec(v_bb_1626_);
    v_res_1630_ =
        lean_llvm_position_builder_at_end(v_ctx_1624_, v_builder_boxed_1628_, v_bb_boxed_1629_);
    return v_res_1630_;
}
pub unsafe fn l_LLVM_buildCall2___boxed(
    mut v_ctx_1638_: *mut leanh::LeanObject,
    mut v_builder_1639_: *mut leanh::LeanObject,
    mut v_ty_1640_: *mut leanh::LeanObject,
    mut v_fn_1641_: *mut leanh::LeanObject,
    mut v_args_1642_: *mut leanh::LeanObject,
    mut v_name_1643_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1645_: usize = 0;
    let mut v_builder_boxed_1646_: usize = 0;
    let mut v_ty_boxed_1647_: usize = 0;
    let mut v_fn_boxed_1648_: usize = 0;
    let mut v_res_1649_: usize = 0;
    let mut v_r_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1645_ = leanh::lean_unbox_usize(v_ctx_1638_);
    leanh::lean_dec(v_ctx_1638_);
    v_builder_boxed_1646_ = leanh::lean_unbox_usize(v_builder_1639_);
    leanh::lean_dec(v_builder_1639_);
    v_ty_boxed_1647_ = leanh::lean_unbox_usize(v_ty_1640_);
    leanh::lean_dec(v_ty_1640_);
    v_fn_boxed_1648_ = leanh::lean_unbox_usize(v_fn_1641_);
    leanh::lean_dec(v_fn_1641_);
    v_res_1649_ = lean_llvm_build_call2(
        v_ctx_boxed_1645_,
        v_builder_boxed_1646_,
        v_ty_boxed_1647_,
        v_fn_boxed_1648_,
        v_args_1642_,
        v_name_1643_,
    );
    leanh::lean_dec_ref(v_args_1642_);
    v_r_1650_ = leanh::lean_box_usize(v_res_1649_);
    return v_r_1650_;
}
pub unsafe fn l_LLVM_setTailCall___boxed(
    mut v_ctx_1655_: *mut leanh::LeanObject,
    mut v_fn_1656_: *mut leanh::LeanObject,
    mut v_istail_1657_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1659_: usize = 0;
    let mut v_fn_boxed_1660_: usize = 0;
    let mut v_istail_boxed_1661_: u8 = 0;
    let mut v_res_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1659_ = leanh::lean_unbox_usize(v_ctx_1655_);
    leanh::lean_dec(v_ctx_1655_);
    v_fn_boxed_1660_ = leanh::lean_unbox_usize(v_fn_1656_);
    leanh::lean_dec(v_fn_1656_);
    v_istail_boxed_1661_ = (leanh::lean_unbox(v_istail_1657_) as u8);
    v_res_1662_ =
        lean_llvm_set_tail_call(v_ctx_boxed_1659_, v_fn_boxed_1660_, v_istail_boxed_1661_);
    return v_res_1662_;
}
pub unsafe fn l_LLVM_buildCondBr___boxed(
    mut v_ctx_1669_: *mut leanh::LeanObject,
    mut v_builder_1670_: *mut leanh::LeanObject,
    mut v_if___1671_: *mut leanh::LeanObject,
    mut v_thenbb_1672_: *mut leanh::LeanObject,
    mut v_elsebb_1673_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1675_: usize = 0;
    let mut v_builder_boxed_1676_: usize = 0;
    let mut v_if___00boxed_1677_: usize = 0;
    let mut v_thenbb_boxed_1678_: usize = 0;
    let mut v_elsebb_boxed_1679_: usize = 0;
    let mut v_res_1680_: usize = 0;
    let mut v_r_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1675_ = leanh::lean_unbox_usize(v_ctx_1669_);
    leanh::lean_dec(v_ctx_1669_);
    v_builder_boxed_1676_ = leanh::lean_unbox_usize(v_builder_1670_);
    leanh::lean_dec(v_builder_1670_);
    v_if___00boxed_1677_ = leanh::lean_unbox_usize(v_if___1671_);
    leanh::lean_dec(v_if___1671_);
    v_thenbb_boxed_1678_ = leanh::lean_unbox_usize(v_thenbb_1672_);
    leanh::lean_dec(v_thenbb_1672_);
    v_elsebb_boxed_1679_ = leanh::lean_unbox_usize(v_elsebb_1673_);
    leanh::lean_dec(v_elsebb_1673_);
    v_res_1680_ = lean_llvm_build_cond_br(
        v_ctx_boxed_1675_,
        v_builder_boxed_1676_,
        v_if___00boxed_1677_,
        v_thenbb_boxed_1678_,
        v_elsebb_boxed_1679_,
    );
    v_r_1681_ = leanh::lean_box_usize(v_res_1680_);
    return v_r_1681_;
}
pub unsafe fn l_LLVM_buildBr___boxed(
    mut v_ctx_1686_: *mut leanh::LeanObject,
    mut v_builder_1687_: *mut leanh::LeanObject,
    mut v_bb_1688_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1690_: usize = 0;
    let mut v_builder_boxed_1691_: usize = 0;
    let mut v_bb_boxed_1692_: usize = 0;
    let mut v_res_1693_: usize = 0;
    let mut v_r_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1690_ = leanh::lean_unbox_usize(v_ctx_1686_);
    leanh::lean_dec(v_ctx_1686_);
    v_builder_boxed_1691_ = leanh::lean_unbox_usize(v_builder_1687_);
    leanh::lean_dec(v_builder_1687_);
    v_bb_boxed_1692_ = leanh::lean_unbox_usize(v_bb_1688_);
    leanh::lean_dec(v_bb_1688_);
    v_res_1693_ = lean_llvm_build_br(v_ctx_boxed_1690_, v_builder_boxed_1691_, v_bb_boxed_1692_);
    v_r_1694_ = leanh::lean_box_usize(v_res_1693_);
    return v_r_1694_;
}
pub unsafe fn l_LLVM_buildAlloca___boxed(
    mut v_ctx_1700_: *mut leanh::LeanObject,
    mut v_builder_1701_: *mut leanh::LeanObject,
    mut v_ty_1702_: *mut leanh::LeanObject,
    mut v_name_1703_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1705_: usize = 0;
    let mut v_builder_boxed_1706_: usize = 0;
    let mut v_ty_boxed_1707_: usize = 0;
    let mut v_res_1708_: usize = 0;
    let mut v_r_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1705_ = leanh::lean_unbox_usize(v_ctx_1700_);
    leanh::lean_dec(v_ctx_1700_);
    v_builder_boxed_1706_ = leanh::lean_unbox_usize(v_builder_1701_);
    leanh::lean_dec(v_builder_1701_);
    v_ty_boxed_1707_ = leanh::lean_unbox_usize(v_ty_1702_);
    leanh::lean_dec(v_ty_1702_);
    v_res_1708_ = lean_llvm_build_alloca(
        v_ctx_boxed_1705_,
        v_builder_boxed_1706_,
        v_ty_boxed_1707_,
        v_name_1703_,
    );
    v_r_1709_ = leanh::lean_box_usize(v_res_1708_);
    return v_r_1709_;
}
pub unsafe fn l_LLVM_buildLoad2___boxed(
    mut v_ctx_1716_: *mut leanh::LeanObject,
    mut v_builder_1717_: *mut leanh::LeanObject,
    mut v_ty_1718_: *mut leanh::LeanObject,
    mut v_val_1719_: *mut leanh::LeanObject,
    mut v_name_1720_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1722_: usize = 0;
    let mut v_builder_boxed_1723_: usize = 0;
    let mut v_ty_boxed_1724_: usize = 0;
    let mut v_val_boxed_1725_: usize = 0;
    let mut v_res_1726_: usize = 0;
    let mut v_r_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1722_ = leanh::lean_unbox_usize(v_ctx_1716_);
    leanh::lean_dec(v_ctx_1716_);
    v_builder_boxed_1723_ = leanh::lean_unbox_usize(v_builder_1717_);
    leanh::lean_dec(v_builder_1717_);
    v_ty_boxed_1724_ = leanh::lean_unbox_usize(v_ty_1718_);
    leanh::lean_dec(v_ty_1718_);
    v_val_boxed_1725_ = leanh::lean_unbox_usize(v_val_1719_);
    leanh::lean_dec(v_val_1719_);
    v_res_1726_ = lean_llvm_build_load2(
        v_ctx_boxed_1722_,
        v_builder_boxed_1723_,
        v_ty_boxed_1724_,
        v_val_boxed_1725_,
        v_name_1720_,
    );
    v_r_1727_ = leanh::lean_box_usize(v_res_1726_);
    return v_r_1727_;
}
pub unsafe fn l_LLVM_buildStore___boxed(
    mut v_ctx_1733_: *mut leanh::LeanObject,
    mut v_builder_1734_: *mut leanh::LeanObject,
    mut v_val_1735_: *mut leanh::LeanObject,
    mut v_store__loc__ptr_1736_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1738_: usize = 0;
    let mut v_builder_boxed_1739_: usize = 0;
    let mut v_val_boxed_1740_: usize = 0;
    let mut v_store__loc__ptr_boxed_1741_: usize = 0;
    let mut v_res_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1738_ = leanh::lean_unbox_usize(v_ctx_1733_);
    leanh::lean_dec(v_ctx_1733_);
    v_builder_boxed_1739_ = leanh::lean_unbox_usize(v_builder_1734_);
    leanh::lean_dec(v_builder_1734_);
    v_val_boxed_1740_ = leanh::lean_unbox_usize(v_val_1735_);
    leanh::lean_dec(v_val_1735_);
    v_store__loc__ptr_boxed_1741_ = leanh::lean_unbox_usize(v_store__loc__ptr_1736_);
    leanh::lean_dec(v_store__loc__ptr_1736_);
    v_res_1742_ = lean_llvm_build_store(
        v_ctx_boxed_1738_,
        v_builder_boxed_1739_,
        v_val_boxed_1740_,
        v_store__loc__ptr_boxed_1741_,
    );
    return v_res_1742_;
}
pub unsafe fn l_LLVM_buildRet___boxed(
    mut v_ctx_1747_: *mut leanh::LeanObject,
    mut v_builder_1748_: *mut leanh::LeanObject,
    mut v_val_1749_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1751_: usize = 0;
    let mut v_builder_boxed_1752_: usize = 0;
    let mut v_val_boxed_1753_: usize = 0;
    let mut v_res_1754_: usize = 0;
    let mut v_r_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1751_ = leanh::lean_unbox_usize(v_ctx_1747_);
    leanh::lean_dec(v_ctx_1747_);
    v_builder_boxed_1752_ = leanh::lean_unbox_usize(v_builder_1748_);
    leanh::lean_dec(v_builder_1748_);
    v_val_boxed_1753_ = leanh::lean_unbox_usize(v_val_1749_);
    leanh::lean_dec(v_val_1749_);
    v_res_1754_ = lean_llvm_build_ret(v_ctx_boxed_1751_, v_builder_boxed_1752_, v_val_boxed_1753_);
    v_r_1755_ = leanh::lean_box_usize(v_res_1754_);
    return v_r_1755_;
}
pub unsafe fn l_LLVM_buildUnreachable___boxed(
    mut v_ctx_1759_: *mut leanh::LeanObject,
    mut v_builder_1760_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1762_: usize = 0;
    let mut v_builder_boxed_1763_: usize = 0;
    let mut v_res_1764_: usize = 0;
    let mut v_r_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1762_ = leanh::lean_unbox_usize(v_ctx_1759_);
    leanh::lean_dec(v_ctx_1759_);
    v_builder_boxed_1763_ = leanh::lean_unbox_usize(v_builder_1760_);
    leanh::lean_dec(v_builder_1760_);
    v_res_1764_ = lean_llvm_build_unreachable(v_ctx_boxed_1762_, v_builder_boxed_1763_);
    v_r_1765_ = leanh::lean_box_usize(v_res_1764_);
    return v_r_1765_;
}
pub unsafe fn l_LLVM_buildGEP2___boxed(
    mut v_ctx_1773_: *mut leanh::LeanObject,
    mut v_builder_1774_: *mut leanh::LeanObject,
    mut v_ty_1775_: *mut leanh::LeanObject,
    mut v_base_1776_: *mut leanh::LeanObject,
    mut v_ixs_1777_: *mut leanh::LeanObject,
    mut v_name_1778_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1780_: usize = 0;
    let mut v_builder_boxed_1781_: usize = 0;
    let mut v_ty_boxed_1782_: usize = 0;
    let mut v_base_boxed_1783_: usize = 0;
    let mut v_res_1784_: usize = 0;
    let mut v_r_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1780_ = leanh::lean_unbox_usize(v_ctx_1773_);
    leanh::lean_dec(v_ctx_1773_);
    v_builder_boxed_1781_ = leanh::lean_unbox_usize(v_builder_1774_);
    leanh::lean_dec(v_builder_1774_);
    v_ty_boxed_1782_ = leanh::lean_unbox_usize(v_ty_1775_);
    leanh::lean_dec(v_ty_1775_);
    v_base_boxed_1783_ = leanh::lean_unbox_usize(v_base_1776_);
    leanh::lean_dec(v_base_1776_);
    v_res_1784_ = lean_llvm_build_gep2(
        v_ctx_boxed_1780_,
        v_builder_boxed_1781_,
        v_ty_boxed_1782_,
        v_base_boxed_1783_,
        v_ixs_1777_,
        v_name_1778_,
    );
    leanh::lean_dec_ref(v_ixs_1777_);
    v_r_1785_ = leanh::lean_box_usize(v_res_1784_);
    return v_r_1785_;
}
pub unsafe fn l_LLVM_buildInBoundsGEP2___boxed(
    mut v_ctx_1793_: *mut leanh::LeanObject,
    mut v_builder_1794_: *mut leanh::LeanObject,
    mut v_ty_1795_: *mut leanh::LeanObject,
    mut v_base_1796_: *mut leanh::LeanObject,
    mut v_ixs_1797_: *mut leanh::LeanObject,
    mut v_name_1798_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1800_: usize = 0;
    let mut v_builder_boxed_1801_: usize = 0;
    let mut v_ty_boxed_1802_: usize = 0;
    let mut v_base_boxed_1803_: usize = 0;
    let mut v_res_1804_: usize = 0;
    let mut v_r_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1800_ = leanh::lean_unbox_usize(v_ctx_1793_);
    leanh::lean_dec(v_ctx_1793_);
    v_builder_boxed_1801_ = leanh::lean_unbox_usize(v_builder_1794_);
    leanh::lean_dec(v_builder_1794_);
    v_ty_boxed_1802_ = leanh::lean_unbox_usize(v_ty_1795_);
    leanh::lean_dec(v_ty_1795_);
    v_base_boxed_1803_ = leanh::lean_unbox_usize(v_base_1796_);
    leanh::lean_dec(v_base_1796_);
    v_res_1804_ = lean_llvm_build_inbounds_gep2(
        v_ctx_boxed_1800_,
        v_builder_boxed_1801_,
        v_ty_boxed_1802_,
        v_base_boxed_1803_,
        v_ixs_1797_,
        v_name_1798_,
    );
    leanh::lean_dec_ref(v_ixs_1797_);
    v_r_1805_ = leanh::lean_box_usize(v_res_1804_);
    return v_r_1805_;
}
pub unsafe fn l_LLVM_buildSext___boxed(
    mut v_ctx_1812_: *mut leanh::LeanObject,
    mut v_builder_1813_: *mut leanh::LeanObject,
    mut v_val_1814_: *mut leanh::LeanObject,
    mut v_destTy_1815_: *mut leanh::LeanObject,
    mut v_name_1816_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1818_: usize = 0;
    let mut v_builder_boxed_1819_: usize = 0;
    let mut v_val_boxed_1820_: usize = 0;
    let mut v_destTy_boxed_1821_: usize = 0;
    let mut v_res_1822_: usize = 0;
    let mut v_r_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1818_ = leanh::lean_unbox_usize(v_ctx_1812_);
    leanh::lean_dec(v_ctx_1812_);
    v_builder_boxed_1819_ = leanh::lean_unbox_usize(v_builder_1813_);
    leanh::lean_dec(v_builder_1813_);
    v_val_boxed_1820_ = leanh::lean_unbox_usize(v_val_1814_);
    leanh::lean_dec(v_val_1814_);
    v_destTy_boxed_1821_ = leanh::lean_unbox_usize(v_destTy_1815_);
    leanh::lean_dec(v_destTy_1815_);
    v_res_1822_ = lean_llvm_build_sext(
        v_ctx_boxed_1818_,
        v_builder_boxed_1819_,
        v_val_boxed_1820_,
        v_destTy_boxed_1821_,
        v_name_1816_,
    );
    v_r_1823_ = leanh::lean_box_usize(v_res_1822_);
    return v_r_1823_;
}
pub unsafe fn l_LLVM_buildZext___boxed(
    mut v_ctx_1830_: *mut leanh::LeanObject,
    mut v_builder_1831_: *mut leanh::LeanObject,
    mut v_val_1832_: *mut leanh::LeanObject,
    mut v_destTy_1833_: *mut leanh::LeanObject,
    mut v_name_1834_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1836_: usize = 0;
    let mut v_builder_boxed_1837_: usize = 0;
    let mut v_val_boxed_1838_: usize = 0;
    let mut v_destTy_boxed_1839_: usize = 0;
    let mut v_res_1840_: usize = 0;
    let mut v_r_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1836_ = leanh::lean_unbox_usize(v_ctx_1830_);
    leanh::lean_dec(v_ctx_1830_);
    v_builder_boxed_1837_ = leanh::lean_unbox_usize(v_builder_1831_);
    leanh::lean_dec(v_builder_1831_);
    v_val_boxed_1838_ = leanh::lean_unbox_usize(v_val_1832_);
    leanh::lean_dec(v_val_1832_);
    v_destTy_boxed_1839_ = leanh::lean_unbox_usize(v_destTy_1833_);
    leanh::lean_dec(v_destTy_1833_);
    v_res_1840_ = lean_llvm_build_zext(
        v_ctx_boxed_1836_,
        v_builder_boxed_1837_,
        v_val_boxed_1838_,
        v_destTy_boxed_1839_,
        v_name_1834_,
    );
    v_r_1841_ = leanh::lean_box_usize(v_res_1840_);
    return v_r_1841_;
}
pub unsafe fn l_LLVM_buildSextOrTrunc___boxed(
    mut v_ctx_1848_: *mut leanh::LeanObject,
    mut v_builder_1849_: *mut leanh::LeanObject,
    mut v_val_1850_: *mut leanh::LeanObject,
    mut v_destTy_1851_: *mut leanh::LeanObject,
    mut v_name_1852_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1854_: usize = 0;
    let mut v_builder_boxed_1855_: usize = 0;
    let mut v_val_boxed_1856_: usize = 0;
    let mut v_destTy_boxed_1857_: usize = 0;
    let mut v_res_1858_: usize = 0;
    let mut v_r_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1854_ = leanh::lean_unbox_usize(v_ctx_1848_);
    leanh::lean_dec(v_ctx_1848_);
    v_builder_boxed_1855_ = leanh::lean_unbox_usize(v_builder_1849_);
    leanh::lean_dec(v_builder_1849_);
    v_val_boxed_1856_ = leanh::lean_unbox_usize(v_val_1850_);
    leanh::lean_dec(v_val_1850_);
    v_destTy_boxed_1857_ = leanh::lean_unbox_usize(v_destTy_1851_);
    leanh::lean_dec(v_destTy_1851_);
    v_res_1858_ = lean_llvm_build_sext_or_trunc(
        v_ctx_boxed_1854_,
        v_builder_boxed_1855_,
        v_val_boxed_1856_,
        v_destTy_boxed_1857_,
        v_name_1852_,
    );
    v_r_1859_ = leanh::lean_box_usize(v_res_1858_);
    return v_r_1859_;
}
pub unsafe fn l_LLVM_buildSwitch___boxed(
    mut v_ctx_1866_: *mut leanh::LeanObject,
    mut v_builder_1867_: *mut leanh::LeanObject,
    mut v_val_1868_: *mut leanh::LeanObject,
    mut v_elseBB_1869_: *mut leanh::LeanObject,
    mut v_numCasesHint_1870_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1872_: usize = 0;
    let mut v_builder_boxed_1873_: usize = 0;
    let mut v_val_boxed_1874_: usize = 0;
    let mut v_elseBB_boxed_1875_: usize = 0;
    let mut v_numCasesHint_boxed_1876_: u64 = 0;
    let mut v_res_1877_: usize = 0;
    let mut v_r_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1872_ = leanh::lean_unbox_usize(v_ctx_1866_);
    leanh::lean_dec(v_ctx_1866_);
    v_builder_boxed_1873_ = leanh::lean_unbox_usize(v_builder_1867_);
    leanh::lean_dec(v_builder_1867_);
    v_val_boxed_1874_ = leanh::lean_unbox_usize(v_val_1868_);
    leanh::lean_dec(v_val_1868_);
    v_elseBB_boxed_1875_ = leanh::lean_unbox_usize(v_elseBB_1869_);
    leanh::lean_dec(v_elseBB_1869_);
    v_numCasesHint_boxed_1876_ = leanh::lean_unbox_uint64(v_numCasesHint_1870_);
    leanh::lean_dec_ref(v_numCasesHint_1870_);
    v_res_1877_ = lean_llvm_build_switch(
        v_ctx_boxed_1872_,
        v_builder_boxed_1873_,
        v_val_boxed_1874_,
        v_elseBB_boxed_1875_,
        v_numCasesHint_boxed_1876_,
    );
    v_r_1878_ = leanh::lean_box_usize(v_res_1877_);
    return v_r_1878_;
}
pub unsafe fn l_LLVM_buildPtrToInt___boxed(
    mut v_ctx_1885_: *mut leanh::LeanObject,
    mut v_builder_1886_: *mut leanh::LeanObject,
    mut v_ptr_1887_: *mut leanh::LeanObject,
    mut v_destTy_1888_: *mut leanh::LeanObject,
    mut v_name_1889_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1891_: usize = 0;
    let mut v_builder_boxed_1892_: usize = 0;
    let mut v_ptr_boxed_1893_: usize = 0;
    let mut v_destTy_boxed_1894_: usize = 0;
    let mut v_res_1895_: usize = 0;
    let mut v_r_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1891_ = leanh::lean_unbox_usize(v_ctx_1885_);
    leanh::lean_dec(v_ctx_1885_);
    v_builder_boxed_1892_ = leanh::lean_unbox_usize(v_builder_1886_);
    leanh::lean_dec(v_builder_1886_);
    v_ptr_boxed_1893_ = leanh::lean_unbox_usize(v_ptr_1887_);
    leanh::lean_dec(v_ptr_1887_);
    v_destTy_boxed_1894_ = leanh::lean_unbox_usize(v_destTy_1888_);
    leanh::lean_dec(v_destTy_1888_);
    v_res_1895_ = lean_llvm_build_ptr_to_int(
        v_ctx_boxed_1891_,
        v_builder_boxed_1892_,
        v_ptr_boxed_1893_,
        v_destTy_boxed_1894_,
        v_name_1889_,
    );
    v_r_1896_ = leanh::lean_box_usize(v_res_1895_);
    return v_r_1896_;
}
pub unsafe fn l_LLVM_buildMul___boxed(
    mut v_ctx_1903_: *mut leanh::LeanObject,
    mut v_builder_1904_: *mut leanh::LeanObject,
    mut v_x_1905_: *mut leanh::LeanObject,
    mut v_y_1906_: *mut leanh::LeanObject,
    mut v_name_1907_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1909_: usize = 0;
    let mut v_builder_boxed_1910_: usize = 0;
    let mut v_x_boxed_1911_: usize = 0;
    let mut v_y_boxed_1912_: usize = 0;
    let mut v_res_1913_: usize = 0;
    let mut v_r_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1909_ = leanh::lean_unbox_usize(v_ctx_1903_);
    leanh::lean_dec(v_ctx_1903_);
    v_builder_boxed_1910_ = leanh::lean_unbox_usize(v_builder_1904_);
    leanh::lean_dec(v_builder_1904_);
    v_x_boxed_1911_ = leanh::lean_unbox_usize(v_x_1905_);
    leanh::lean_dec(v_x_1905_);
    v_y_boxed_1912_ = leanh::lean_unbox_usize(v_y_1906_);
    leanh::lean_dec(v_y_1906_);
    v_res_1913_ = lean_llvm_build_mul(
        v_ctx_boxed_1909_,
        v_builder_boxed_1910_,
        v_x_boxed_1911_,
        v_y_boxed_1912_,
        v_name_1907_,
    );
    v_r_1914_ = leanh::lean_box_usize(v_res_1913_);
    return v_r_1914_;
}
pub unsafe fn l_LLVM_buildAdd___boxed(
    mut v_ctx_1921_: *mut leanh::LeanObject,
    mut v_builder_1922_: *mut leanh::LeanObject,
    mut v_x_1923_: *mut leanh::LeanObject,
    mut v_y_1924_: *mut leanh::LeanObject,
    mut v_name_1925_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1927_: usize = 0;
    let mut v_builder_boxed_1928_: usize = 0;
    let mut v_x_boxed_1929_: usize = 0;
    let mut v_y_boxed_1930_: usize = 0;
    let mut v_res_1931_: usize = 0;
    let mut v_r_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1927_ = leanh::lean_unbox_usize(v_ctx_1921_);
    leanh::lean_dec(v_ctx_1921_);
    v_builder_boxed_1928_ = leanh::lean_unbox_usize(v_builder_1922_);
    leanh::lean_dec(v_builder_1922_);
    v_x_boxed_1929_ = leanh::lean_unbox_usize(v_x_1923_);
    leanh::lean_dec(v_x_1923_);
    v_y_boxed_1930_ = leanh::lean_unbox_usize(v_y_1924_);
    leanh::lean_dec(v_y_1924_);
    v_res_1931_ = lean_llvm_build_add(
        v_ctx_boxed_1927_,
        v_builder_boxed_1928_,
        v_x_boxed_1929_,
        v_y_boxed_1930_,
        v_name_1925_,
    );
    v_r_1932_ = leanh::lean_box_usize(v_res_1931_);
    return v_r_1932_;
}
pub unsafe fn l_LLVM_buildSub___boxed(
    mut v_ctx_1939_: *mut leanh::LeanObject,
    mut v_builder_1940_: *mut leanh::LeanObject,
    mut v_x_1941_: *mut leanh::LeanObject,
    mut v_y_1942_: *mut leanh::LeanObject,
    mut v_name_1943_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1945_: usize = 0;
    let mut v_builder_boxed_1946_: usize = 0;
    let mut v_x_boxed_1947_: usize = 0;
    let mut v_y_boxed_1948_: usize = 0;
    let mut v_res_1949_: usize = 0;
    let mut v_r_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1945_ = leanh::lean_unbox_usize(v_ctx_1939_);
    leanh::lean_dec(v_ctx_1939_);
    v_builder_boxed_1946_ = leanh::lean_unbox_usize(v_builder_1940_);
    leanh::lean_dec(v_builder_1940_);
    v_x_boxed_1947_ = leanh::lean_unbox_usize(v_x_1941_);
    leanh::lean_dec(v_x_1941_);
    v_y_boxed_1948_ = leanh::lean_unbox_usize(v_y_1942_);
    leanh::lean_dec(v_y_1942_);
    v_res_1949_ = lean_llvm_build_sub(
        v_ctx_boxed_1945_,
        v_builder_boxed_1946_,
        v_x_boxed_1947_,
        v_y_boxed_1948_,
        v_name_1943_,
    );
    v_r_1950_ = leanh::lean_box_usize(v_res_1949_);
    return v_r_1950_;
}
pub unsafe fn l_LLVM_buildNot___boxed(
    mut v_ctx_1956_: *mut leanh::LeanObject,
    mut v_builder_1957_: *mut leanh::LeanObject,
    mut v_x_1958_: *mut leanh::LeanObject,
    mut v_name_1959_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1961_: usize = 0;
    let mut v_builder_boxed_1962_: usize = 0;
    let mut v_x_boxed_1963_: usize = 0;
    let mut v_res_1964_: usize = 0;
    let mut v_r_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1961_ = leanh::lean_unbox_usize(v_ctx_1956_);
    leanh::lean_dec(v_ctx_1956_);
    v_builder_boxed_1962_ = leanh::lean_unbox_usize(v_builder_1957_);
    leanh::lean_dec(v_builder_1957_);
    v_x_boxed_1963_ = leanh::lean_unbox_usize(v_x_1958_);
    leanh::lean_dec(v_x_1958_);
    v_res_1964_ = lean_llvm_build_not(
        v_ctx_boxed_1961_,
        v_builder_boxed_1962_,
        v_x_boxed_1963_,
        v_name_1959_,
    );
    v_r_1965_ = leanh::lean_box_usize(v_res_1964_);
    return v_r_1965_;
}
pub unsafe fn l_LLVM_buildICmp___boxed(
    mut v_ctx_1973_: *mut leanh::LeanObject,
    mut v_builder_1974_: *mut leanh::LeanObject,
    mut v_predicate_1975_: *mut leanh::LeanObject,
    mut v_x_1976_: *mut leanh::LeanObject,
    mut v_y_1977_: *mut leanh::LeanObject,
    mut v_name_1978_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1980_: usize = 0;
    let mut v_builder_boxed_1981_: usize = 0;
    let mut v_predicate_boxed_1982_: u64 = 0;
    let mut v_x_boxed_1983_: usize = 0;
    let mut v_y_boxed_1984_: usize = 0;
    let mut v_res_1985_: usize = 0;
    let mut v_r_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1980_ = leanh::lean_unbox_usize(v_ctx_1973_);
    leanh::lean_dec(v_ctx_1973_);
    v_builder_boxed_1981_ = leanh::lean_unbox_usize(v_builder_1974_);
    leanh::lean_dec(v_builder_1974_);
    v_predicate_boxed_1982_ = leanh::lean_unbox_uint64(v_predicate_1975_);
    leanh::lean_dec_ref(v_predicate_1975_);
    v_x_boxed_1983_ = leanh::lean_unbox_usize(v_x_1976_);
    leanh::lean_dec(v_x_1976_);
    v_y_boxed_1984_ = leanh::lean_unbox_usize(v_y_1977_);
    leanh::lean_dec(v_y_1977_);
    v_res_1985_ = lean_llvm_build_icmp(
        v_ctx_boxed_1980_,
        v_builder_boxed_1981_,
        v_predicate_boxed_1982_,
        v_x_boxed_1983_,
        v_y_boxed_1984_,
        v_name_1978_,
    );
    v_r_1986_ = leanh::lean_box_usize(v_res_1985_);
    return v_r_1986_;
}
pub unsafe fn l_LLVM_addCase___boxed(
    mut v_ctx_1992_: *mut leanh::LeanObject,
    mut v_switch_1993_: *mut leanh::LeanObject,
    mut v_onVal_1994_: *mut leanh::LeanObject,
    mut v_destBB_1995_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_1997_: usize = 0;
    let mut v_switch_boxed_1998_: usize = 0;
    let mut v_onVal_boxed_1999_: usize = 0;
    let mut v_destBB_boxed_2000_: usize = 0;
    let mut v_res_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_1997_ = leanh::lean_unbox_usize(v_ctx_1992_);
    leanh::lean_dec(v_ctx_1992_);
    v_switch_boxed_1998_ = leanh::lean_unbox_usize(v_switch_1993_);
    leanh::lean_dec(v_switch_1993_);
    v_onVal_boxed_1999_ = leanh::lean_unbox_usize(v_onVal_1994_);
    leanh::lean_dec(v_onVal_1994_);
    v_destBB_boxed_2000_ = leanh::lean_unbox_usize(v_destBB_1995_);
    leanh::lean_dec(v_destBB_1995_);
    v_res_2001_ = lean_llvm_add_case(
        v_ctx_boxed_1997_,
        v_switch_boxed_1998_,
        v_onVal_boxed_1999_,
        v_destBB_boxed_2000_,
    );
    return v_res_2001_;
}
pub unsafe fn l_LLVM_getInsertBlock___boxed(
    mut v_Context_00___x40_Lean_Compiler_IR_LLVMBindings_924321998____hygCtx___hyg_2006_: *mut leanh::LeanObject,
    mut v_ctx_2007_: *mut leanh::LeanObject,
    mut v_builder_2008_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_builder_boxed_2010_: usize = 0;
    let mut v_res_2011_: usize = 0;
    let mut v_r_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_builder_boxed_2010_ = leanh::lean_unbox_usize(v_builder_2008_);
    leanh::lean_dec(v_builder_2008_);
    v_res_2011_ = lean_llvm_get_insert_block(v_ctx_2007_, v_builder_boxed_2010_);
    v_r_2012_ = leanh::lean_box_usize(v_res_2011_);
    return v_r_2012_;
}
pub unsafe fn l_LLVM_clearInsertionPosition___boxed(
    mut v_Context_00___x40_Lean_Compiler_IR_LLVMBindings_1700267677____hygCtx___hyg_2017_: *mut leanh::LeanObject,
    mut v_ctx_2018_: *mut leanh::LeanObject,
    mut v_builder_2019_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_builder_boxed_2021_: usize = 0;
    let mut v_res_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_builder_boxed_2021_ = leanh::lean_unbox_usize(v_builder_2019_);
    leanh::lean_dec(v_builder_2019_);
    v_res_2022_ = lean_llvm_clear_insertion_position(v_ctx_2018_, v_builder_boxed_2021_);
    return v_res_2022_;
}
pub unsafe fn l_LLVM_getBasicBlockParent___boxed(
    mut v_ctx_2026_: *mut leanh::LeanObject,
    mut v_bb_2027_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2029_: usize = 0;
    let mut v_bb_boxed_2030_: usize = 0;
    let mut v_res_2031_: usize = 0;
    let mut v_r_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2029_ = leanh::lean_unbox_usize(v_ctx_2026_);
    leanh::lean_dec(v_ctx_2026_);
    v_bb_boxed_2030_ = leanh::lean_unbox_usize(v_bb_2027_);
    leanh::lean_dec(v_bb_2027_);
    v_res_2031_ = lean_llvm_get_basic_block_parent(v_ctx_boxed_2029_, v_bb_boxed_2030_);
    v_r_2032_ = leanh::lean_box_usize(v_res_2031_);
    return v_r_2032_;
}
pub unsafe fn l_LLVM_typeOf___boxed(
    mut v_ctx_2036_: *mut leanh::LeanObject,
    mut v_val_2037_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2039_: usize = 0;
    let mut v_val_boxed_2040_: usize = 0;
    let mut v_res_2041_: usize = 0;
    let mut v_r_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2039_ = leanh::lean_unbox_usize(v_ctx_2036_);
    leanh::lean_dec(v_ctx_2036_);
    v_val_boxed_2040_ = leanh::lean_unbox_usize(v_val_2037_);
    leanh::lean_dec(v_val_2037_);
    v_res_2041_ = lean_llvm_type_of(v_ctx_boxed_2039_, v_val_boxed_2040_);
    v_r_2042_ = leanh::lean_box_usize(v_res_2041_);
    return v_r_2042_;
}
pub unsafe fn l_LLVM_constInt___boxed(
    mut v_ctx_2048_: *mut leanh::LeanObject,
    mut v_intty_2049_: *mut leanh::LeanObject,
    mut v_value_2050_: *mut leanh::LeanObject,
    mut v_signExtend_2051_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2053_: usize = 0;
    let mut v_intty_boxed_2054_: usize = 0;
    let mut v_value_boxed_2055_: u64 = 0;
    let mut v_signExtend_boxed_2056_: u8 = 0;
    let mut v_res_2057_: usize = 0;
    let mut v_r_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2053_ = leanh::lean_unbox_usize(v_ctx_2048_);
    leanh::lean_dec(v_ctx_2048_);
    v_intty_boxed_2054_ = leanh::lean_unbox_usize(v_intty_2049_);
    leanh::lean_dec(v_intty_2049_);
    v_value_boxed_2055_ = leanh::lean_unbox_uint64(v_value_2050_);
    leanh::lean_dec_ref(v_value_2050_);
    v_signExtend_boxed_2056_ = (leanh::lean_unbox(v_signExtend_2051_) as u8);
    v_res_2057_ = lean_llvm_const_int(
        v_ctx_boxed_2053_,
        v_intty_boxed_2054_,
        v_value_boxed_2055_,
        v_signExtend_boxed_2056_,
    );
    v_r_2058_ = leanh::lean_box_usize(v_res_2057_);
    return v_r_2058_;
}
pub unsafe fn l_LLVM_printModuletoString___boxed(
    mut v_ctx_2062_: *mut leanh::LeanObject,
    mut v_mod_2063_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2065_: usize = 0;
    let mut v_mod_boxed_2066_: usize = 0;
    let mut v_res_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2065_ = leanh::lean_unbox_usize(v_ctx_2062_);
    leanh::lean_dec(v_ctx_2062_);
    v_mod_boxed_2066_ = leanh::lean_unbox_usize(v_mod_2063_);
    leanh::lean_dec(v_mod_2063_);
    v_res_2067_ = lean_llvm_print_module_to_string(v_ctx_boxed_2065_, v_mod_boxed_2066_);
    return v_res_2067_;
}
pub unsafe fn l_LLVM_printModuletoFile___boxed(
    mut v_ctx_2072_: *mut leanh::LeanObject,
    mut v_mod_2073_: *mut leanh::LeanObject,
    mut v_file_2074_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2076_: usize = 0;
    let mut v_mod_boxed_2077_: usize = 0;
    let mut v_res_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2076_ = leanh::lean_unbox_usize(v_ctx_2072_);
    leanh::lean_dec(v_ctx_2072_);
    v_mod_boxed_2077_ = leanh::lean_unbox_usize(v_mod_2073_);
    leanh::lean_dec(v_mod_2073_);
    v_res_2078_ =
        lean_llvm_print_module_to_file(v_ctx_boxed_2076_, v_mod_boxed_2077_, v_file_2074_);
    leanh::lean_dec_ref(v_file_2074_);
    return v_res_2078_;
}
pub unsafe fn l_LLVM_countParams___boxed(
    mut v_ctx_2082_: *mut leanh::LeanObject,
    mut v_fn_2083_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2085_: usize = 0;
    let mut v_fn_boxed_2086_: usize = 0;
    let mut v_res_2087_: u64 = 0;
    let mut v_r_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2085_ = leanh::lean_unbox_usize(v_ctx_2082_);
    leanh::lean_dec(v_ctx_2082_);
    v_fn_boxed_2086_ = leanh::lean_unbox_usize(v_fn_2083_);
    leanh::lean_dec(v_fn_2083_);
    v_res_2087_ = llvm_count_params(v_ctx_boxed_2085_, v_fn_boxed_2086_);
    v_r_2088_ = leanh::lean_box_uint64(v_res_2087_);
    return v_r_2088_;
}
pub unsafe fn l_LLVM_getParam___boxed(
    mut v_ctx_2093_: *mut leanh::LeanObject,
    mut v_fn_2094_: *mut leanh::LeanObject,
    mut v_ix_2095_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2097_: usize = 0;
    let mut v_fn_boxed_2098_: usize = 0;
    let mut v_ix_boxed_2099_: u64 = 0;
    let mut v_res_2100_: usize = 0;
    let mut v_r_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2097_ = leanh::lean_unbox_usize(v_ctx_2093_);
    leanh::lean_dec(v_ctx_2093_);
    v_fn_boxed_2098_ = leanh::lean_unbox_usize(v_fn_2094_);
    leanh::lean_dec(v_fn_2094_);
    v_ix_boxed_2099_ = leanh::lean_unbox_uint64(v_ix_2095_);
    leanh::lean_dec_ref(v_ix_2095_);
    v_res_2100_ = llvm_get_param(v_ctx_boxed_2097_, v_fn_boxed_2098_, v_ix_boxed_2099_);
    v_r_2101_ = leanh::lean_box_usize(v_res_2100_);
    return v_r_2101_;
}
pub unsafe fn l_LLVM_createMemoryBufferWithContentsOfFile___boxed(
    mut v_ctx_2105_: *mut leanh::LeanObject,
    mut v_path_2106_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2108_: usize = 0;
    let mut v_res_2109_: usize = 0;
    let mut v_r_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2108_ = leanh::lean_unbox_usize(v_ctx_2105_);
    leanh::lean_dec(v_ctx_2105_);
    v_res_2109_ =
        lean_llvm_create_memory_buffer_with_contents_of_file(v_ctx_boxed_2108_, v_path_2106_);
    leanh::lean_dec_ref(v_path_2106_);
    v_r_2110_ = leanh::lean_box_usize(v_res_2109_);
    return v_r_2110_;
}
pub unsafe fn l_LLVM_parseBitcode___boxed(
    mut v_ctx_2114_: *mut leanh::LeanObject,
    mut v_membuf_2115_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2117_: usize = 0;
    let mut v_membuf_boxed_2118_: usize = 0;
    let mut v_res_2119_: usize = 0;
    let mut v_r_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2117_ = leanh::lean_unbox_usize(v_ctx_2114_);
    leanh::lean_dec(v_ctx_2114_);
    v_membuf_boxed_2118_ = leanh::lean_unbox_usize(v_membuf_2115_);
    leanh::lean_dec(v_membuf_2115_);
    v_res_2119_ = lean_llvm_parse_bitcode(v_ctx_boxed_2117_, v_membuf_boxed_2118_);
    v_r_2120_ = leanh::lean_box_usize(v_res_2119_);
    return v_r_2120_;
}
pub unsafe fn l_LLVM_linkModules___boxed(
    mut v_ctx_2125_: *mut leanh::LeanObject,
    mut v_dest_2126_: *mut leanh::LeanObject,
    mut v_src_2127_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2129_: usize = 0;
    let mut v_dest_boxed_2130_: usize = 0;
    let mut v_src_boxed_2131_: usize = 0;
    let mut v_res_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2129_ = leanh::lean_unbox_usize(v_ctx_2125_);
    leanh::lean_dec(v_ctx_2125_);
    v_dest_boxed_2130_ = leanh::lean_unbox_usize(v_dest_2126_);
    leanh::lean_dec(v_dest_2126_);
    v_src_boxed_2131_ = leanh::lean_unbox_usize(v_src_2127_);
    leanh::lean_dec(v_src_2127_);
    v_res_2132_ = lean_llvm_link_modules(v_ctx_boxed_2129_, v_dest_boxed_2130_, v_src_boxed_2131_);
    return v_res_2132_;
}
pub unsafe fn l_LLVM_getDefaultTargetTriple___boxed(
    mut v_a_00___x40___internal___hyg_2134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2135_ = lean_llvm_get_default_target_triple();
    return v_res_2135_;
}
pub unsafe fn l_LLVM_getTargetFromTriple___boxed(
    mut v_ctx_2139_: *mut leanh::LeanObject,
    mut v_triple_2140_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2142_: usize = 0;
    let mut v_res_2143_: usize = 0;
    let mut v_r_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2142_ = leanh::lean_unbox_usize(v_ctx_2139_);
    leanh::lean_dec(v_ctx_2139_);
    v_res_2143_ = lean_llvm_get_target_from_triple(v_ctx_boxed_2142_, v_triple_2140_);
    leanh::lean_dec_ref(v_triple_2140_);
    v_r_2144_ = leanh::lean_box_usize(v_res_2143_);
    return v_r_2144_;
}
pub unsafe fn l_LLVM_createTargetMachine___boxed(
    mut v_ctx_2151_: *mut leanh::LeanObject,
    mut v_target_2152_: *mut leanh::LeanObject,
    mut v_tripleStr_2153_: *mut leanh::LeanObject,
    mut v_cpu_2154_: *mut leanh::LeanObject,
    mut v_features_2155_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2157_: usize = 0;
    let mut v_target_boxed_2158_: usize = 0;
    let mut v_res_2159_: usize = 0;
    let mut v_r_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2157_ = leanh::lean_unbox_usize(v_ctx_2151_);
    leanh::lean_dec(v_ctx_2151_);
    v_target_boxed_2158_ = leanh::lean_unbox_usize(v_target_2152_);
    leanh::lean_dec(v_target_2152_);
    v_res_2159_ = lean_llvm_create_target_machine(
        v_ctx_boxed_2157_,
        v_target_boxed_2158_,
        v_tripleStr_2153_,
        v_cpu_2154_,
        v_features_2155_,
    );
    leanh::lean_dec_ref(v_features_2155_);
    leanh::lean_dec_ref(v_cpu_2154_);
    leanh::lean_dec_ref(v_tripleStr_2153_);
    v_r_2160_ = leanh::lean_box_usize(v_res_2159_);
    return v_r_2160_;
}
pub unsafe fn l_LLVM_targetMachineEmitToFile___boxed(
    mut v_ctx_2167_: *mut leanh::LeanObject,
    mut v_targetMachine_2168_: *mut leanh::LeanObject,
    mut v_module_2169_: *mut leanh::LeanObject,
    mut v_filepath_2170_: *mut leanh::LeanObject,
    mut v_codegenType_2171_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2173_: usize = 0;
    let mut v_targetMachine_boxed_2174_: usize = 0;
    let mut v_module_boxed_2175_: usize = 0;
    let mut v_codegenType_boxed_2176_: u64 = 0;
    let mut v_res_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2173_ = leanh::lean_unbox_usize(v_ctx_2167_);
    leanh::lean_dec(v_ctx_2167_);
    v_targetMachine_boxed_2174_ = leanh::lean_unbox_usize(v_targetMachine_2168_);
    leanh::lean_dec(v_targetMachine_2168_);
    v_module_boxed_2175_ = leanh::lean_unbox_usize(v_module_2169_);
    leanh::lean_dec(v_module_2169_);
    v_codegenType_boxed_2176_ = leanh::lean_unbox_uint64(v_codegenType_2171_);
    leanh::lean_dec_ref(v_codegenType_2171_);
    v_res_2177_ = lean_llvm_target_machine_emit_to_file(
        v_ctx_boxed_2173_,
        v_targetMachine_boxed_2174_,
        v_module_boxed_2175_,
        v_filepath_2170_,
        v_codegenType_boxed_2176_,
    );
    leanh::lean_dec_ref(v_filepath_2170_);
    return v_res_2177_;
}
pub unsafe fn l_LLVM_disposeTargetMachine___boxed(
    mut v_ctx_2181_: *mut leanh::LeanObject,
    mut v_tm_2182_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2184_: usize = 0;
    let mut v_tm_boxed_2185_: usize = 0;
    let mut v_res_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2184_ = leanh::lean_unbox_usize(v_ctx_2181_);
    leanh::lean_dec(v_ctx_2181_);
    v_tm_boxed_2185_ = leanh::lean_unbox_usize(v_tm_2182_);
    leanh::lean_dec(v_tm_2182_);
    v_res_2186_ = lean_llvm_dispose_target_machine(v_ctx_boxed_2184_, v_tm_boxed_2185_);
    return v_res_2186_;
}
pub unsafe fn l_LLVM_disposeModule___boxed(
    mut v_ctx_2190_: *mut leanh::LeanObject,
    mut v_m_2191_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2193_: usize = 0;
    let mut v_m_boxed_2194_: usize = 0;
    let mut v_res_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2193_ = leanh::lean_unbox_usize(v_ctx_2190_);
    leanh::lean_dec(v_ctx_2190_);
    v_m_boxed_2194_ = leanh::lean_unbox_usize(v_m_2191_);
    leanh::lean_dec(v_m_2191_);
    v_res_2195_ = lean_llvm_dispose_module(v_ctx_boxed_2193_, v_m_boxed_2194_);
    return v_res_2195_;
}
pub unsafe fn l_LLVM_verifyModule___boxed(
    mut v_ctx_2199_: *mut leanh::LeanObject,
    mut v_m_2200_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2202_: usize = 0;
    let mut v_m_boxed_2203_: usize = 0;
    let mut v_res_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2202_ = leanh::lean_unbox_usize(v_ctx_2199_);
    leanh::lean_dec(v_ctx_2199_);
    v_m_boxed_2203_ = leanh::lean_unbox_usize(v_m_2200_);
    leanh::lean_dec(v_m_2200_);
    v_res_2204_ = lean_llvm_verify_module(v_ctx_boxed_2202_, v_m_boxed_2203_);
    return v_res_2204_;
}
pub unsafe fn l_LLVM_createStringAttribute___boxed(
    mut v_ctx_2209_: *mut leanh::LeanObject,
    mut v_key_2210_: *mut leanh::LeanObject,
    mut v_value_2211_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2213_: usize = 0;
    let mut v_res_2214_: usize = 0;
    let mut v_r_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2213_ = leanh::lean_unbox_usize(v_ctx_2209_);
    leanh::lean_dec(v_ctx_2209_);
    v_res_2214_ = lean_llvm_create_string_attribute(v_ctx_boxed_2213_, v_key_2210_, v_value_2211_);
    v_r_2215_ = leanh::lean_box_usize(v_res_2214_);
    return v_r_2215_;
}
pub unsafe fn l_LLVM_addAttributeAtIndex___boxed(
    mut v_ctx_2221_: *mut leanh::LeanObject,
    mut v_fn_2222_: *mut leanh::LeanObject,
    mut v_idx_2223_: *mut leanh::LeanObject,
    mut v_attr_2224_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2226_: usize = 0;
    let mut v_fn_boxed_2227_: usize = 0;
    let mut v_idx_boxed_2228_: u64 = 0;
    let mut v_attr_boxed_2229_: usize = 0;
    let mut v_res_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2226_ = leanh::lean_unbox_usize(v_ctx_2221_);
    leanh::lean_dec(v_ctx_2221_);
    v_fn_boxed_2227_ = leanh::lean_unbox_usize(v_fn_2222_);
    leanh::lean_dec(v_fn_2222_);
    v_idx_boxed_2228_ = leanh::lean_unbox_uint64(v_idx_2223_);
    leanh::lean_dec_ref(v_idx_2223_);
    v_attr_boxed_2229_ = leanh::lean_unbox_usize(v_attr_2224_);
    leanh::lean_dec(v_attr_2224_);
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
    mut v_ctx_2238_: *mut leanh::LeanObject,
    mut v_value_2239_: *mut leanh::LeanObject,
    mut v_visibility_2240_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2242_: usize = 0;
    let mut v_value_boxed_2243_: usize = 0;
    let mut v_visibility_boxed_2244_: u64 = 0;
    let mut v_res_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2242_ = leanh::lean_unbox_usize(v_ctx_2238_);
    leanh::lean_dec(v_ctx_2238_);
    v_value_boxed_2243_ = leanh::lean_unbox_usize(v_value_2239_);
    leanh::lean_dec(v_value_2239_);
    v_visibility_boxed_2244_ = leanh::lean_unbox_uint64(v_visibility_2240_);
    leanh::lean_dec_ref(v_visibility_2240_);
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
    mut v_ctx_2253_: *mut leanh::LeanObject,
    mut v_value_2254_: *mut leanh::LeanObject,
    mut v_dllStorageClass_2255_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2257_: usize = 0;
    let mut v_value_boxed_2258_: usize = 0;
    let mut v_dllStorageClass_boxed_2259_: u64 = 0;
    let mut v_res_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2257_ = leanh::lean_unbox_usize(v_ctx_2253_);
    leanh::lean_dec(v_ctx_2253_);
    v_value_boxed_2258_ = leanh::lean_unbox_usize(v_value_2254_);
    leanh::lean_dec(v_value_2254_);
    v_dllStorageClass_boxed_2259_ = leanh::lean_unbox_uint64(v_dllStorageClass_2255_);
    leanh::lean_dec_ref(v_dllStorageClass_2255_);
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
    mut v_ctx_2282_: *mut leanh::LeanObject,
    mut v_value_2283_: *mut leanh::LeanObject,
    mut v_linkage_2284_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_2285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2286_: usize = 0;
    let mut v_value_boxed_2287_: usize = 0;
    let mut v_linkage_boxed_2288_: u64 = 0;
    let mut v_res_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2286_ = leanh::lean_unbox_usize(v_ctx_2282_);
    leanh::lean_dec(v_ctx_2282_);
    v_value_boxed_2287_ = leanh::lean_unbox_usize(v_value_2283_);
    leanh::lean_dec(v_value_2283_);
    v_linkage_boxed_2288_ = leanh::lean_unbox_uint64(v_linkage_2284_);
    leanh::lean_dec_ref(v_linkage_2284_);
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
    mut v_ctx_2294_: *mut leanh::LeanObject,
    mut v_a_2295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2296_: usize = 0;
    let mut v_res_2297_: usize = 0;
    let mut v_r_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2296_ = leanh::lean_unbox_usize(v_ctx_2294_);
    leanh::lean_dec(v_ctx_2294_);
    v_res_2297_ = l_LLVM_i1Type(v_ctx_boxed_2296_);
    v_r_2298_ = leanh::lean_box_usize(v_res_2297_);
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
    mut v_ctx_2303_: *mut leanh::LeanObject,
    mut v_a_2304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2305_: usize = 0;
    let mut v_res_2306_: usize = 0;
    let mut v_r_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2305_ = leanh::lean_unbox_usize(v_ctx_2303_);
    leanh::lean_dec(v_ctx_2303_);
    v_res_2306_ = l_LLVM_i8Type(v_ctx_boxed_2305_);
    v_r_2307_ = leanh::lean_box_usize(v_res_2306_);
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
    mut v_ctx_2312_: *mut leanh::LeanObject,
    mut v_a_2313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2314_: usize = 0;
    let mut v_res_2315_: usize = 0;
    let mut v_r_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2314_ = leanh::lean_unbox_usize(v_ctx_2312_);
    leanh::lean_dec(v_ctx_2312_);
    v_res_2315_ = l_LLVM_i16Type(v_ctx_boxed_2314_);
    v_r_2316_ = leanh::lean_box_usize(v_res_2315_);
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
    mut v_ctx_2321_: *mut leanh::LeanObject,
    mut v_a_2322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2323_: usize = 0;
    let mut v_res_2324_: usize = 0;
    let mut v_r_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2323_ = leanh::lean_unbox_usize(v_ctx_2321_);
    leanh::lean_dec(v_ctx_2321_);
    v_res_2324_ = l_LLVM_i32Type(v_ctx_boxed_2323_);
    v_r_2325_ = leanh::lean_box_usize(v_res_2324_);
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
    mut v_ctx_2330_: *mut leanh::LeanObject,
    mut v_a_2331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2332_: usize = 0;
    let mut v_res_2333_: usize = 0;
    let mut v_r_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2332_ = leanh::lean_unbox_usize(v_ctx_2330_);
    leanh::lean_dec(v_ctx_2330_);
    v_res_2333_ = l_LLVM_i64Type(v_ctx_boxed_2332_);
    v_r_2334_ = leanh::lean_box_usize(v_res_2333_);
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
    mut v_ctx_2340_: *mut leanh::LeanObject,
    mut v_a_2341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2342_: usize = 0;
    let mut v_res_2343_: usize = 0;
    let mut v_r_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2342_ = leanh::lean_unbox_usize(v_ctx_2340_);
    leanh::lean_dec(v_ctx_2340_);
    v_res_2343_ = l_LLVM_voidPtrType(v_ctx_boxed_2342_);
    v_r_2344_ = leanh::lean_box_usize(v_res_2343_);
    return v_r_2344_;
}
pub unsafe fn l_LLVM_i8PtrType(mut v_ctx_2345_: usize) -> usize {
    let mut v___x_2347_: usize = 0;
    v___x_2347_ = l_LLVM_voidPtrType(v_ctx_2345_);
    return v___x_2347_;
}
pub unsafe fn l_LLVM_i8PtrType___boxed(
    mut v_ctx_2348_: *mut leanh::LeanObject,
    mut v_a_2349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2350_: usize = 0;
    let mut v_res_2351_: usize = 0;
    let mut v_r_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2350_ = leanh::lean_unbox_usize(v_ctx_2348_);
    leanh::lean_dec(v_ctx_2348_);
    v_res_2351_ = l_LLVM_i8PtrType(v_ctx_boxed_2350_);
    v_r_2352_ = leanh::lean_box_usize(v_res_2351_);
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
    mut v_ctx_2359_: *mut leanh::LeanObject,
    mut v_a_2360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2361_: usize = 0;
    let mut v_res_2362_: usize = 0;
    let mut v_r_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2361_ = leanh::lean_unbox_usize(v_ctx_2359_);
    leanh::lean_dec(v_ctx_2359_);
    v_res_2362_ = l_LLVM_constTrue(v_ctx_boxed_2361_);
    v_r_2363_ = leanh::lean_box_usize(v_res_2362_);
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
    mut v_ctx_2370_: *mut leanh::LeanObject,
    mut v_a_2371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2372_: usize = 0;
    let mut v_res_2373_: usize = 0;
    let mut v_r_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2372_ = leanh::lean_unbox_usize(v_ctx_2370_);
    leanh::lean_dec(v_ctx_2370_);
    v_res_2373_ = l_LLVM_constFalse(v_ctx_boxed_2372_);
    v_r_2374_ = leanh::lean_box_usize(v_res_2373_);
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
    mut v_ctx_2382_: *mut leanh::LeanObject,
    mut v_width_2383_: *mut leanh::LeanObject,
    mut v_value_2384_: *mut leanh::LeanObject,
    mut v_signExtend_2385_: *mut leanh::LeanObject,
    mut v_a_2386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2387_: usize = 0;
    let mut v_width_boxed_2388_: u64 = 0;
    let mut v_value_boxed_2389_: u64 = 0;
    let mut v_signExtend_boxed_2390_: u8 = 0;
    let mut v_res_2391_: usize = 0;
    let mut v_r_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2387_ = leanh::lean_unbox_usize(v_ctx_2382_);
    leanh::lean_dec(v_ctx_2382_);
    v_width_boxed_2388_ = leanh::lean_unbox_uint64(v_width_2383_);
    leanh::lean_dec_ref(v_width_2383_);
    v_value_boxed_2389_ = leanh::lean_unbox_uint64(v_value_2384_);
    leanh::lean_dec_ref(v_value_2384_);
    v_signExtend_boxed_2390_ = (leanh::lean_unbox(v_signExtend_2385_) as u8);
    v_res_2391_ = l_LLVM_constInt_x27(
        v_ctx_boxed_2387_,
        v_width_boxed_2388_,
        v_value_boxed_2389_,
        v_signExtend_boxed_2390_,
    );
    v_r_2392_ = leanh::lean_box_usize(v_res_2391_);
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
    mut v_ctx_2399_: *mut leanh::LeanObject,
    mut v_value_2400_: *mut leanh::LeanObject,
    mut v_signExtend_2401_: *mut leanh::LeanObject,
    mut v_a_2402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2403_: usize = 0;
    let mut v_value_boxed_2404_: u64 = 0;
    let mut v_signExtend_boxed_2405_: u8 = 0;
    let mut v_res_2406_: usize = 0;
    let mut v_r_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2403_ = leanh::lean_unbox_usize(v_ctx_2399_);
    leanh::lean_dec(v_ctx_2399_);
    v_value_boxed_2404_ = leanh::lean_unbox_uint64(v_value_2400_);
    leanh::lean_dec_ref(v_value_2400_);
    v_signExtend_boxed_2405_ = (leanh::lean_unbox(v_signExtend_2401_) as u8);
    v_res_2406_ = l_LLVM_constInt1(
        v_ctx_boxed_2403_,
        v_value_boxed_2404_,
        v_signExtend_boxed_2405_,
    );
    v_r_2407_ = leanh::lean_box_usize(v_res_2406_);
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
    mut v_ctx_2414_: *mut leanh::LeanObject,
    mut v_value_2415_: *mut leanh::LeanObject,
    mut v_signExtend_2416_: *mut leanh::LeanObject,
    mut v_a_2417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2418_: usize = 0;
    let mut v_value_boxed_2419_: u64 = 0;
    let mut v_signExtend_boxed_2420_: u8 = 0;
    let mut v_res_2421_: usize = 0;
    let mut v_r_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2418_ = leanh::lean_unbox_usize(v_ctx_2414_);
    leanh::lean_dec(v_ctx_2414_);
    v_value_boxed_2419_ = leanh::lean_unbox_uint64(v_value_2415_);
    leanh::lean_dec_ref(v_value_2415_);
    v_signExtend_boxed_2420_ = (leanh::lean_unbox(v_signExtend_2416_) as u8);
    v_res_2421_ = l_LLVM_constInt8(
        v_ctx_boxed_2418_,
        v_value_boxed_2419_,
        v_signExtend_boxed_2420_,
    );
    v_r_2422_ = leanh::lean_box_usize(v_res_2421_);
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
    mut v_ctx_2429_: *mut leanh::LeanObject,
    mut v_value_2430_: *mut leanh::LeanObject,
    mut v_signExtend_2431_: *mut leanh::LeanObject,
    mut v_a_2432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2433_: usize = 0;
    let mut v_value_boxed_2434_: u64 = 0;
    let mut v_signExtend_boxed_2435_: u8 = 0;
    let mut v_res_2436_: usize = 0;
    let mut v_r_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2433_ = leanh::lean_unbox_usize(v_ctx_2429_);
    leanh::lean_dec(v_ctx_2429_);
    v_value_boxed_2434_ = leanh::lean_unbox_uint64(v_value_2430_);
    leanh::lean_dec_ref(v_value_2430_);
    v_signExtend_boxed_2435_ = (leanh::lean_unbox(v_signExtend_2431_) as u8);
    v_res_2436_ = l_LLVM_constInt32(
        v_ctx_boxed_2433_,
        v_value_boxed_2434_,
        v_signExtend_boxed_2435_,
    );
    v_r_2437_ = leanh::lean_box_usize(v_res_2436_);
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
    mut v_ctx_2444_: *mut leanh::LeanObject,
    mut v_value_2445_: *mut leanh::LeanObject,
    mut v_signExtend_2446_: *mut leanh::LeanObject,
    mut v_a_2447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2448_: usize = 0;
    let mut v_value_boxed_2449_: u64 = 0;
    let mut v_signExtend_boxed_2450_: u8 = 0;
    let mut v_res_2451_: usize = 0;
    let mut v_r_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2448_ = leanh::lean_unbox_usize(v_ctx_2444_);
    leanh::lean_dec(v_ctx_2444_);
    v_value_boxed_2449_ = leanh::lean_unbox_uint64(v_value_2445_);
    leanh::lean_dec_ref(v_value_2445_);
    v_signExtend_boxed_2450_ = (leanh::lean_unbox(v_signExtend_2446_) as u8);
    v_res_2451_ = l_LLVM_constInt64(
        v_ctx_boxed_2448_,
        v_value_boxed_2449_,
        v_signExtend_boxed_2450_,
    );
    v_r_2452_ = leanh::lean_box_usize(v_res_2451_);
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
    mut v_ctx_2459_: *mut leanh::LeanObject,
    mut v_value_2460_: *mut leanh::LeanObject,
    mut v_signExtend_2461_: *mut leanh::LeanObject,
    mut v_a_2462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2463_: usize = 0;
    let mut v_value_boxed_2464_: u64 = 0;
    let mut v_signExtend_boxed_2465_: u8 = 0;
    let mut v_res_2466_: usize = 0;
    let mut v_r_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2463_ = leanh::lean_unbox_usize(v_ctx_2459_);
    leanh::lean_dec(v_ctx_2459_);
    v_value_boxed_2464_ = leanh::lean_unbox_uint64(v_value_2460_);
    leanh::lean_dec_ref(v_value_2460_);
    v_signExtend_boxed_2465_ = (leanh::lean_unbox(v_signExtend_2461_) as u8);
    v_res_2466_ = l_LLVM_constIntSizeT(
        v_ctx_boxed_2463_,
        v_value_boxed_2464_,
        v_signExtend_boxed_2465_,
    );
    v_r_2467_ = leanh::lean_box_usize(v_res_2466_);
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
    mut v_ctx_2474_: *mut leanh::LeanObject,
    mut v_value_2475_: *mut leanh::LeanObject,
    mut v_signExtend_2476_: *mut leanh::LeanObject,
    mut v_a_2477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_boxed_2478_: usize = 0;
    let mut v_value_boxed_2479_: u64 = 0;
    let mut v_signExtend_boxed_2480_: u8 = 0;
    let mut v_res_2481_: usize = 0;
    let mut v_r_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_boxed_2478_ = leanh::lean_unbox_usize(v_ctx_2474_);
    leanh::lean_dec(v_ctx_2474_);
    v_value_boxed_2479_ = leanh::lean_unbox_uint64(v_value_2475_);
    leanh::lean_dec_ref(v_value_2475_);
    v_signExtend_boxed_2480_ = (leanh::lean_unbox(v_signExtend_2476_) as u8);
    v_res_2481_ = l_LLVM_constIntUnsigned(
        v_ctx_boxed_2478_,
        v_value_boxed_2479_,
        v_signExtend_boxed_2480_,
    );
    v_r_2482_ = leanh::lean_box_usize(v_res_2481_);
    return v_r_2482_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_LLVMBindings(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
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
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_LLVMBindings(
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
pub unsafe fn initialize_Lean_Compiler_IR_LLVMBindings(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_LLVMBindings(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_LLVMBindings(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_LLVMBindings(builtin);
}