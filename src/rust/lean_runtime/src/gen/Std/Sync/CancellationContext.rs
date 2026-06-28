// Lean compiler output
// Module: Std.Sync.CancellationContext
// Imports: Std.Sync.CancellationToken Init.Data.Ord.UInt
use crate::r#gen::Init::Core::l_Prod_map___redArg;
use crate::r#gen::Init::Data::Ord::UInt::{
    initialize_Init_Data_Ord_UInt, runtime_initialize_Init_Data_Ord_UInt,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_maxView___redArg, l_Std_DTreeMap_Internal_Impl_minView___redArg,
};
use crate::r#gen::Std::Sync::CancellationToken::{
    initialize_Std_Sync_CancellationToken, l_Std_CancellationToken_cancel,
    l_Std_CancellationToken_getCancellationReason, l_Std_CancellationToken_isCancelled,
    l_Std_CancellationToken_new, l_Std_CancellationToken_selector, l_Std_CancellationToken_wait,
    runtime_initialize_Std_Sync_CancellationToken,
};
use crate::r#gen::Std::Sync::Mutex::l_Std_Mutex_new___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{lean_uint64_add, lean_uint64_dec_lt};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_uint64_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_get, lean_st_ref_set};
use crate::lean_imports_rs::Std::Sync::Mutex::{lean_io_basemutex_lock, lean_io_basemutex_unlock};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2, lean_box,
    lean_box_uint64, lean_closure_set, lean_ctor_get, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_tag, lean_unbox_uint64, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Std_CancellationContext_new___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Std_CancellationContext_new___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationContext_new___closed__0_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(
    mut v_k_1324_: u64,
    mut v_v_1325_: *mut LeanObject,
    mut v_t_1326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1334_: u8 = 0;
    let mut v___x_1335_: u64 = 0;
    let mut v___x_1336_: u8 = 0;
    let mut v___x_1337_: u64 = 0;
    let mut v___x_1338_: u8 = 0;
    let mut v_impl_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: u8 = 0;
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1357_: u8 = 0;
    let mut v_size_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: u8 = 0;
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1394_: u8 = 0;
    let mut v_unused_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1411_: u8 = 0;
    let mut v_unused_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1418_: u8 = 0;
    let mut v_unused_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v_k_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1435_: u8 = 0;
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1446_: u8 = 0;
    let mut v_unused_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1450_: u8 = 0;
    let mut v_unused_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1458_: u8 = 0;
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1466_: u8 = 0;
    let mut v_unused_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: u8 = 0;
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1496_: u8 = 0;
    let mut v_size_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: u8 = 0;
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1508_: u8 = 0;
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1534_: u8 = 0;
    let mut v_unused_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1548_: u8 = 0;
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1552_: u8 = 0;
    let mut v_unused_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1559_: u8 = 0;
    let mut v_unused_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1571_: u8 = 0;
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1579_: u8 = 0;
    let mut v_unused_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1587_: u8 = 0;
    let mut v_k_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1592_: u8 = 0;
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut v_unused_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1607_: u8 = 0;
    let mut v_unused_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1615_: u8 = 0;
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1326_) == 0 {
                    v_size_1327_ = lean_ctor_get(v_t_1326_, 0);
                    v_k_1328_ = lean_ctor_get(v_t_1326_, 1);
                    v_v_1329_ = lean_ctor_get(v_t_1326_, 2);
                    v_l_1330_ = lean_ctor_get(v_t_1326_, 3);
                    v_r_1331_ = lean_ctor_get(v_t_1326_, 4);
                    v_isSharedCheck_1615_ = (!lean_is_exclusive(v_t_1326_)) as u8;
                    if v_isSharedCheck_1615_ == 0 {
                        v___x_1333_ = v_t_1326_;
                        v_isShared_1334_ = v_isSharedCheck_1615_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_1331_);
                        lean_inc(v_l_1330_);
                        lean_inc(v_v_1329_);
                        lean_inc(v_k_1328_);
                        lean_inc(v_size_1327_);
                        lean_dec(v_t_1326_);
                        v___x_1333_ = lean_box(0);
                        v_isShared_1334_ = v_isSharedCheck_1615_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1616_ = lean_unsigned_to_nat(1);
                    v___x_1617_ = lean_box_uint64(v_k_1324_);
                    v___x_1618_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_1618_, 0, v___x_1616_);
                    lean_ctor_set(v___x_1618_, 1, v___x_1617_);
                    lean_ctor_set(v___x_1618_, 2, v_v_1325_);
                    lean_ctor_set(v___x_1618_, 3, v_t_1326_);
                    lean_ctor_set(v___x_1618_, 4, v_t_1326_);
                    return v___x_1618_;
                }
            }
            1 => {
                v___x_1335_ = lean_unbox_uint64(v_k_1328_);
                v___x_1336_ = lean_uint64_dec_lt(v_k_1324_, v___x_1335_);
                if v___x_1336_ == 0 {
                    v___x_1337_ = lean_unbox_uint64(v_k_1328_);
                    v___x_1338_ = lean_uint64_dec_eq(v_k_1324_, v___x_1337_);
                    if v___x_1338_ == 0 {
                        lean_dec(v_size_1327_);
                        v_impl_1339_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_k_1324_, v_v_1325_, v_r_1331_);
                        v___x_1340_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_1330_) == 0 {
                            v_size_1341_ = lean_ctor_get(v_l_1330_, 0);
                            v_size_1342_ = lean_ctor_get(v_impl_1339_, 0);
                            lean_inc(v_size_1342_);
                            v_k_1343_ = lean_ctor_get(v_impl_1339_, 1);
                            lean_inc(v_k_1343_);
                            v_v_1344_ = lean_ctor_get(v_impl_1339_, 2);
                            lean_inc(v_v_1344_);
                            v_l_1345_ = lean_ctor_get(v_impl_1339_, 3);
                            lean_inc(v_l_1345_);
                            v_r_1346_ = lean_ctor_get(v_impl_1339_, 4);
                            lean_inc(v_r_1346_);
                            v___x_1347_ = lean_unsigned_to_nat(3);
                            v___x_1348_ = lean_nat_mul(v___x_1347_, v_size_1341_);
                            v___x_1349_ = lean_nat_dec_lt(v___x_1348_, v_size_1342_);
                            lean_dec(v___x_1348_);
                            if v___x_1349_ == 0 {
                                lean_dec(v_r_1346_);
                                lean_dec(v_l_1345_);
                                lean_dec(v_v_1344_);
                                lean_dec(v_k_1343_);
                                v___x_1350_ = lean_nat_add(v___x_1340_, v_size_1341_);
                                v___x_1351_ = lean_nat_add(v___x_1350_, v_size_1342_);
                                lean_dec(v_size_1342_);
                                lean_dec(v___x_1350_);
                                if v_isShared_1334_ == 0 {
                                    lean_ctor_set(v___x_1333_, 4, v_impl_1339_);
                                    lean_ctor_set(v___x_1333_, 0, v___x_1351_);
                                    v___x_1353_ = v___x_1333_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
                                    lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_k_1328_);
                                    lean_ctor_set(v_reuseFailAlloc_1354_, 2, v_v_1329_);
                                    lean_ctor_set(v_reuseFailAlloc_1354_, 3, v_l_1330_);
                                    lean_ctor_set(v_reuseFailAlloc_1354_, 4, v_impl_1339_);
                                    v___x_1353_ = v_reuseFailAlloc_1354_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1418_ = (!lean_is_exclusive(v_impl_1339_)) as u8;
                                if v_isSharedCheck_1418_ == 0 {
                                    v_unused_1419_ = lean_ctor_get(v_impl_1339_, 4);
                                    lean_dec(v_unused_1419_);
                                    v_unused_1420_ = lean_ctor_get(v_impl_1339_, 3);
                                    lean_dec(v_unused_1420_);
                                    v_unused_1421_ = lean_ctor_get(v_impl_1339_, 2);
                                    lean_dec(v_unused_1421_);
                                    v_unused_1422_ = lean_ctor_get(v_impl_1339_, 1);
                                    lean_dec(v_unused_1422_);
                                    v_unused_1423_ = lean_ctor_get(v_impl_1339_, 0);
                                    lean_dec(v_unused_1423_);
                                    v___x_1356_ = v_impl_1339_;
                                    v_isShared_1357_ = v_isSharedCheck_1418_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_1339_);
                                    v___x_1356_ = lean_box(0);
                                    v_isShared_1357_ = v_isSharedCheck_1418_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1424_ = lean_ctor_get(v_impl_1339_, 3);
                            lean_inc(v_l_1424_);
                            if lean_obj_tag(v_l_1424_) == 0 {
                                v_r_1425_ = lean_ctor_get(v_impl_1339_, 4);
                                v_k_1426_ = lean_ctor_get(v_impl_1339_, 1);
                                v_v_1427_ = lean_ctor_get(v_impl_1339_, 2);
                                v_isSharedCheck_1450_ = (!lean_is_exclusive(v_impl_1339_)) as u8;
                                if v_isSharedCheck_1450_ == 0 {
                                    v_unused_1451_ = lean_ctor_get(v_impl_1339_, 3);
                                    lean_dec(v_unused_1451_);
                                    v_unused_1452_ = lean_ctor_get(v_impl_1339_, 0);
                                    lean_dec(v_unused_1452_);
                                    v___x_1429_ = v_impl_1339_;
                                    v_isShared_1430_ = v_isSharedCheck_1450_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_1425_);
                                    lean_inc(v_v_1427_);
                                    lean_inc(v_k_1426_);
                                    lean_dec(v_impl_1339_);
                                    v___x_1429_ = lean_box(0);
                                    v_isShared_1430_ = v_isSharedCheck_1450_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1453_ = lean_ctor_get(v_impl_1339_, 4);
                                lean_inc(v_r_1453_);
                                if lean_obj_tag(v_r_1453_) == 0 {
                                    v_k_1454_ = lean_ctor_get(v_impl_1339_, 1);
                                    v_v_1455_ = lean_ctor_get(v_impl_1339_, 2);
                                    v_isSharedCheck_1466_ =
                                        (!lean_is_exclusive(v_impl_1339_)) as u8;
                                    if v_isSharedCheck_1466_ == 0 {
                                        v_unused_1467_ = lean_ctor_get(v_impl_1339_, 4);
                                        lean_dec(v_unused_1467_);
                                        v_unused_1468_ = lean_ctor_get(v_impl_1339_, 3);
                                        lean_dec(v_unused_1468_);
                                        v_unused_1469_ = lean_ctor_get(v_impl_1339_, 0);
                                        lean_dec(v_unused_1469_);
                                        v___x_1457_ = v_impl_1339_;
                                        v_isShared_1458_ = v_isSharedCheck_1466_;
                                        state = 18;
                                        continue;
                                    } else {
                                        lean_inc(v_v_1455_);
                                        lean_inc(v_k_1454_);
                                        lean_dec(v_impl_1339_);
                                        v___x_1457_ = lean_box(0);
                                        v_isShared_1458_ = v_isSharedCheck_1466_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_1470_ = lean_unsigned_to_nat(2);
                                    if v_isShared_1334_ == 0 {
                                        lean_ctor_set(v___x_1333_, 4, v_impl_1339_);
                                        lean_ctor_set(v___x_1333_, 3, v_r_1453_);
                                        lean_ctor_set(v___x_1333_, 0, v___x_1470_);
                                        v___x_1472_ = v___x_1333_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
                                        lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_k_1328_);
                                        lean_ctor_set(v_reuseFailAlloc_1473_, 2, v_v_1329_);
                                        lean_ctor_set(v_reuseFailAlloc_1473_, 3, v_r_1453_);
                                        lean_ctor_set(v_reuseFailAlloc_1473_, 4, v_impl_1339_);
                                        v___x_1472_ = v_reuseFailAlloc_1473_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_v_1329_);
                        lean_dec(v_k_1328_);
                        v___x_1474_ = lean_box_uint64(v_k_1324_);
                        if v_isShared_1334_ == 0 {
                            lean_ctor_set(v___x_1333_, 2, v_v_1325_);
                            lean_ctor_set(v___x_1333_, 1, v___x_1474_);
                            v___x_1476_ = v___x_1333_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_size_1327_);
                            lean_ctor_set(v_reuseFailAlloc_1477_, 1, v___x_1474_);
                            lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_v_1325_);
                            lean_ctor_set(v_reuseFailAlloc_1477_, 3, v_l_1330_);
                            lean_ctor_set(v_reuseFailAlloc_1477_, 4, v_r_1331_);
                            v___x_1476_ = v_reuseFailAlloc_1477_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_size_1327_);
                    v_impl_1478_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_k_1324_, v_v_1325_, v_l_1330_);
                    v___x_1479_ = lean_unsigned_to_nat(1);
                    if lean_obj_tag(v_r_1331_) == 0 {
                        v_size_1480_ = lean_ctor_get(v_r_1331_, 0);
                        v_size_1481_ = lean_ctor_get(v_impl_1478_, 0);
                        lean_inc(v_size_1481_);
                        v_k_1482_ = lean_ctor_get(v_impl_1478_, 1);
                        lean_inc(v_k_1482_);
                        v_v_1483_ = lean_ctor_get(v_impl_1478_, 2);
                        lean_inc(v_v_1483_);
                        v_l_1484_ = lean_ctor_get(v_impl_1478_, 3);
                        lean_inc(v_l_1484_);
                        v_r_1485_ = lean_ctor_get(v_impl_1478_, 4);
                        lean_inc(v_r_1485_);
                        v___x_1486_ = lean_unsigned_to_nat(3);
                        v___x_1487_ = lean_nat_mul(v___x_1486_, v_size_1480_);
                        v___x_1488_ = lean_nat_dec_lt(v___x_1487_, v_size_1481_);
                        lean_dec(v___x_1487_);
                        if v___x_1488_ == 0 {
                            lean_dec(v_r_1485_);
                            lean_dec(v_l_1484_);
                            lean_dec(v_v_1483_);
                            lean_dec(v_k_1482_);
                            v___x_1489_ = lean_nat_add(v___x_1479_, v_size_1481_);
                            lean_dec(v_size_1481_);
                            v___x_1490_ = lean_nat_add(v___x_1489_, v_size_1480_);
                            lean_dec(v___x_1489_);
                            if v_isShared_1334_ == 0 {
                                lean_ctor_set(v___x_1333_, 3, v_impl_1478_);
                                lean_ctor_set(v___x_1333_, 0, v___x_1490_);
                                v___x_1492_ = v___x_1333_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
                                lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_k_1328_);
                                lean_ctor_set(v_reuseFailAlloc_1493_, 2, v_v_1329_);
                                lean_ctor_set(v_reuseFailAlloc_1493_, 3, v_impl_1478_);
                                lean_ctor_set(v_reuseFailAlloc_1493_, 4, v_r_1331_);
                                v___x_1492_ = v_reuseFailAlloc_1493_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_1559_ = (!lean_is_exclusive(v_impl_1478_)) as u8;
                            if v_isSharedCheck_1559_ == 0 {
                                v_unused_1560_ = lean_ctor_get(v_impl_1478_, 4);
                                lean_dec(v_unused_1560_);
                                v_unused_1561_ = lean_ctor_get(v_impl_1478_, 3);
                                lean_dec(v_unused_1561_);
                                v_unused_1562_ = lean_ctor_get(v_impl_1478_, 2);
                                lean_dec(v_unused_1562_);
                                v_unused_1563_ = lean_ctor_get(v_impl_1478_, 1);
                                lean_dec(v_unused_1563_);
                                v_unused_1564_ = lean_ctor_get(v_impl_1478_, 0);
                                lean_dec(v_unused_1564_);
                                v___x_1495_ = v_impl_1478_;
                                v_isShared_1496_ = v_isSharedCheck_1559_;
                                state = 24;
                                continue;
                            } else {
                                lean_dec(v_impl_1478_);
                                v___x_1495_ = lean_box(0);
                                v_isShared_1496_ = v_isSharedCheck_1559_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_1565_ = lean_ctor_get(v_impl_1478_, 3);
                        lean_inc(v_l_1565_);
                        if lean_obj_tag(v_l_1565_) == 0 {
                            v_r_1566_ = lean_ctor_get(v_impl_1478_, 4);
                            v_k_1567_ = lean_ctor_get(v_impl_1478_, 1);
                            v_v_1568_ = lean_ctor_get(v_impl_1478_, 2);
                            v_isSharedCheck_1579_ = (!lean_is_exclusive(v_impl_1478_)) as u8;
                            if v_isSharedCheck_1579_ == 0 {
                                v_unused_1580_ = lean_ctor_get(v_impl_1478_, 3);
                                lean_dec(v_unused_1580_);
                                v_unused_1581_ = lean_ctor_get(v_impl_1478_, 0);
                                lean_dec(v_unused_1581_);
                                v___x_1570_ = v_impl_1478_;
                                v_isShared_1571_ = v_isSharedCheck_1579_;
                                state = 34;
                                continue;
                            } else {
                                lean_inc(v_r_1566_);
                                lean_inc(v_v_1568_);
                                lean_inc(v_k_1567_);
                                lean_dec(v_impl_1478_);
                                v___x_1570_ = lean_box(0);
                                v_isShared_1571_ = v_isSharedCheck_1579_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_1582_ = lean_ctor_get(v_impl_1478_, 4);
                            lean_inc(v_r_1582_);
                            if lean_obj_tag(v_r_1582_) == 0 {
                                v_k_1583_ = lean_ctor_get(v_impl_1478_, 1);
                                v_v_1584_ = lean_ctor_get(v_impl_1478_, 2);
                                v_isSharedCheck_1607_ = (!lean_is_exclusive(v_impl_1478_)) as u8;
                                if v_isSharedCheck_1607_ == 0 {
                                    v_unused_1608_ = lean_ctor_get(v_impl_1478_, 4);
                                    lean_dec(v_unused_1608_);
                                    v_unused_1609_ = lean_ctor_get(v_impl_1478_, 3);
                                    lean_dec(v_unused_1609_);
                                    v_unused_1610_ = lean_ctor_get(v_impl_1478_, 0);
                                    lean_dec(v_unused_1610_);
                                    v___x_1586_ = v_impl_1478_;
                                    v_isShared_1587_ = v_isSharedCheck_1607_;
                                    state = 37;
                                    continue;
                                } else {
                                    lean_inc(v_v_1584_);
                                    lean_inc(v_k_1583_);
                                    lean_dec(v_impl_1478_);
                                    v___x_1586_ = lean_box(0);
                                    v_isShared_1587_ = v_isSharedCheck_1607_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_1611_ = lean_unsigned_to_nat(2);
                                if v_isShared_1334_ == 0 {
                                    lean_ctor_set(v___x_1333_, 4, v_r_1582_);
                                    lean_ctor_set(v___x_1333_, 3, v_impl_1478_);
                                    lean_ctor_set(v___x_1333_, 0, v___x_1611_);
                                    v___x_1613_ = v___x_1333_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
                                    lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_k_1328_);
                                    lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_v_1329_);
                                    lean_ctor_set(v_reuseFailAlloc_1614_, 3, v_impl_1478_);
                                    lean_ctor_set(v_reuseFailAlloc_1614_, 4, v_r_1582_);
                                    v___x_1613_ = v_reuseFailAlloc_1614_;
                                    state = 42;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1353_;
            }
            3 => {
                v_size_1358_ = lean_ctor_get(v_l_1345_, 0);
                v_k_1359_ = lean_ctor_get(v_l_1345_, 1);
                v_v_1360_ = lean_ctor_get(v_l_1345_, 2);
                v_l_1361_ = lean_ctor_get(v_l_1345_, 3);
                v_r_1362_ = lean_ctor_get(v_l_1345_, 4);
                v_size_1363_ = lean_ctor_get(v_r_1346_, 0);
                v___x_1364_ = lean_unsigned_to_nat(2);
                v___x_1365_ = lean_nat_mul(v___x_1364_, v_size_1363_);
                v___x_1366_ = lean_nat_dec_lt(v_size_1358_, v___x_1365_);
                lean_dec(v___x_1365_);
                if v___x_1366_ == 0 {
                    lean_inc(v_r_1362_);
                    lean_inc(v_l_1361_);
                    lean_inc(v_v_1360_);
                    lean_inc(v_k_1359_);
                    v_isSharedCheck_1394_ = (!lean_is_exclusive(v_l_1345_)) as u8;
                    if v_isSharedCheck_1394_ == 0 {
                        v_unused_1395_ = lean_ctor_get(v_l_1345_, 4);
                        lean_dec(v_unused_1395_);
                        v_unused_1396_ = lean_ctor_get(v_l_1345_, 3);
                        lean_dec(v_unused_1396_);
                        v_unused_1397_ = lean_ctor_get(v_l_1345_, 2);
                        lean_dec(v_unused_1397_);
                        v_unused_1398_ = lean_ctor_get(v_l_1345_, 1);
                        lean_dec(v_unused_1398_);
                        v_unused_1399_ = lean_ctor_get(v_l_1345_, 0);
                        lean_dec(v_unused_1399_);
                        v___x_1368_ = v_l_1345_;
                        v_isShared_1369_ = v_isSharedCheck_1394_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_l_1345_);
                        v___x_1368_ = lean_box(0);
                        v_isShared_1369_ = v_isSharedCheck_1394_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1333_);
                    v___x_1400_ = lean_nat_add(v___x_1340_, v_size_1341_);
                    v___x_1401_ = lean_nat_add(v___x_1400_, v_size_1342_);
                    lean_dec(v_size_1342_);
                    v___x_1402_ = lean_nat_add(v___x_1400_, v_size_1358_);
                    lean_dec(v___x_1400_);
                    lean_inc_ref(v_l_1330_);
                    if v_isShared_1357_ == 0 {
                        lean_ctor_set(v___x_1356_, 4, v_l_1345_);
                        lean_ctor_set(v___x_1356_, 3, v_l_1330_);
                        lean_ctor_set(v___x_1356_, 2, v_v_1329_);
                        lean_ctor_set(v___x_1356_, 1, v_k_1328_);
                        lean_ctor_set(v___x_1356_, 0, v___x_1402_);
                        v___x_1404_ = v___x_1356_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1402_);
                        lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1328_);
                        lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1329_);
                        lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_l_1330_);
                        lean_ctor_set(v_reuseFailAlloc_1417_, 4, v_l_1345_);
                        v___x_1404_ = v_reuseFailAlloc_1417_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1370_ = lean_nat_add(v___x_1340_, v_size_1341_);
                v___x_1371_ = lean_nat_add(v___x_1370_, v_size_1342_);
                lean_dec(v_size_1342_);
                if lean_obj_tag(v_l_1361_) == 0 {
                    v_size_1392_ = lean_ctor_get(v_l_1361_, 0);
                    lean_inc(v_size_1392_);
                    v___y_1384_ = v_size_1392_;
                    state = 8;
                    continue;
                } else {
                    v___x_1393_ = lean_unsigned_to_nat(0);
                    v___y_1384_ = v___x_1393_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1376_ = lean_nat_add(v___y_1373_, v___y_1375_);
                lean_dec(v___y_1375_);
                lean_dec(v___y_1373_);
                if v_isShared_1369_ == 0 {
                    lean_ctor_set(v___x_1368_, 4, v_r_1346_);
                    lean_ctor_set(v___x_1368_, 3, v_r_1362_);
                    lean_ctor_set(v___x_1368_, 2, v_v_1344_);
                    lean_ctor_set(v___x_1368_, 1, v_k_1343_);
                    lean_ctor_set(v___x_1368_, 0, v___x_1376_);
                    v___x_1378_ = v___x_1368_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1376_);
                    lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_k_1343_);
                    lean_ctor_set(v_reuseFailAlloc_1382_, 2, v_v_1344_);
                    lean_ctor_set(v_reuseFailAlloc_1382_, 3, v_r_1362_);
                    lean_ctor_set(v_reuseFailAlloc_1382_, 4, v_r_1346_);
                    v___x_1378_ = v_reuseFailAlloc_1382_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1357_ == 0 {
                    lean_ctor_set(v___x_1356_, 4, v___x_1378_);
                    lean_ctor_set(v___x_1356_, 3, v___y_1374_);
                    lean_ctor_set(v___x_1356_, 2, v_v_1360_);
                    lean_ctor_set(v___x_1356_, 1, v_k_1359_);
                    lean_ctor_set(v___x_1356_, 0, v___x_1371_);
                    v___x_1380_ = v___x_1356_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1371_);
                    lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_k_1359_);
                    lean_ctor_set(v_reuseFailAlloc_1381_, 2, v_v_1360_);
                    lean_ctor_set(v_reuseFailAlloc_1381_, 3, v___y_1374_);
                    lean_ctor_set(v_reuseFailAlloc_1381_, 4, v___x_1378_);
                    v___x_1380_ = v_reuseFailAlloc_1381_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1380_;
            }
            8 => {
                v___x_1385_ = lean_nat_add(v___x_1370_, v___y_1384_);
                lean_dec(v___y_1384_);
                lean_dec(v___x_1370_);
                if v_isShared_1334_ == 0 {
                    lean_ctor_set(v___x_1333_, 4, v_l_1361_);
                    lean_ctor_set(v___x_1333_, 0, v___x_1385_);
                    v___x_1387_ = v___x_1333_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1385_);
                    lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_k_1328_);
                    lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_v_1329_);
                    lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_l_1330_);
                    lean_ctor_set(v_reuseFailAlloc_1391_, 4, v_l_1361_);
                    v___x_1387_ = v_reuseFailAlloc_1391_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1388_ = lean_nat_add(v___x_1340_, v_size_1363_);
                if lean_obj_tag(v_r_1362_) == 0 {
                    v_size_1389_ = lean_ctor_get(v_r_1362_, 0);
                    lean_inc(v_size_1389_);
                    v___y_1373_ = v___x_1388_;
                    v___y_1374_ = v___x_1387_;
                    v___y_1375_ = v_size_1389_;
                    state = 5;
                    continue;
                } else {
                    v___x_1390_ = lean_unsigned_to_nat(0);
                    v___y_1373_ = v___x_1388_;
                    v___y_1374_ = v___x_1387_;
                    v___y_1375_ = v___x_1390_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1411_ = (!lean_is_exclusive(v_l_1330_)) as u8;
                if v_isSharedCheck_1411_ == 0 {
                    v_unused_1412_ = lean_ctor_get(v_l_1330_, 4);
                    lean_dec(v_unused_1412_);
                    v_unused_1413_ = lean_ctor_get(v_l_1330_, 3);
                    lean_dec(v_unused_1413_);
                    v_unused_1414_ = lean_ctor_get(v_l_1330_, 2);
                    lean_dec(v_unused_1414_);
                    v_unused_1415_ = lean_ctor_get(v_l_1330_, 1);
                    lean_dec(v_unused_1415_);
                    v_unused_1416_ = lean_ctor_get(v_l_1330_, 0);
                    lean_dec(v_unused_1416_);
                    v___x_1406_ = v_l_1330_;
                    v_isShared_1407_ = v_isSharedCheck_1411_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_l_1330_);
                    v___x_1406_ = lean_box(0);
                    v_isShared_1407_ = v_isSharedCheck_1411_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1407_ == 0 {
                    lean_ctor_set(v___x_1406_, 4, v_r_1346_);
                    lean_ctor_set(v___x_1406_, 3, v___x_1404_);
                    lean_ctor_set(v___x_1406_, 2, v_v_1344_);
                    lean_ctor_set(v___x_1406_, 1, v_k_1343_);
                    lean_ctor_set(v___x_1406_, 0, v___x_1401_);
                    v___x_1409_ = v___x_1406_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1401_);
                    lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_k_1343_);
                    lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_v_1344_);
                    lean_ctor_set(v_reuseFailAlloc_1410_, 3, v___x_1404_);
                    lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_r_1346_);
                    v___x_1409_ = v_reuseFailAlloc_1410_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1409_;
            }
            13 => {
                v_k_1431_ = lean_ctor_get(v_l_1424_, 1);
                v_v_1432_ = lean_ctor_get(v_l_1424_, 2);
                v_isSharedCheck_1446_ = (!lean_is_exclusive(v_l_1424_)) as u8;
                if v_isSharedCheck_1446_ == 0 {
                    v_unused_1447_ = lean_ctor_get(v_l_1424_, 4);
                    lean_dec(v_unused_1447_);
                    v_unused_1448_ = lean_ctor_get(v_l_1424_, 3);
                    lean_dec(v_unused_1448_);
                    v_unused_1449_ = lean_ctor_get(v_l_1424_, 0);
                    lean_dec(v_unused_1449_);
                    v___x_1434_ = v_l_1424_;
                    v_isShared_1435_ = v_isSharedCheck_1446_;
                    state = 14;
                    continue;
                } else {
                    lean_inc(v_v_1432_);
                    lean_inc(v_k_1431_);
                    lean_dec(v_l_1424_);
                    v___x_1434_ = lean_box(0);
                    v_isShared_1435_ = v_isSharedCheck_1446_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_1436_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_1425_, 2);
                if v_isShared_1435_ == 0 {
                    lean_ctor_set(v___x_1434_, 4, v_r_1425_);
                    lean_ctor_set(v___x_1434_, 3, v_r_1425_);
                    lean_ctor_set(v___x_1434_, 2, v_v_1329_);
                    lean_ctor_set(v___x_1434_, 1, v_k_1328_);
                    lean_ctor_set(v___x_1434_, 0, v___x_1340_);
                    v___x_1438_ = v___x_1434_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1340_);
                    lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_k_1328_);
                    lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_v_1329_);
                    lean_ctor_set(v_reuseFailAlloc_1445_, 3, v_r_1425_);
                    lean_ctor_set(v_reuseFailAlloc_1445_, 4, v_r_1425_);
                    v___x_1438_ = v_reuseFailAlloc_1445_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                lean_inc(v_r_1425_);
                if v_isShared_1430_ == 0 {
                    lean_ctor_set(v___x_1429_, 3, v_r_1425_);
                    lean_ctor_set(v___x_1429_, 0, v___x_1340_);
                    v___x_1440_ = v___x_1429_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1340_);
                    lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_k_1426_);
                    lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_v_1427_);
                    lean_ctor_set(v_reuseFailAlloc_1444_, 3, v_r_1425_);
                    lean_ctor_set(v_reuseFailAlloc_1444_, 4, v_r_1425_);
                    v___x_1440_ = v_reuseFailAlloc_1444_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_1334_ == 0 {
                    lean_ctor_set(v___x_1333_, 4, v___x_1440_);
                    lean_ctor_set(v___x_1333_, 3, v___x_1438_);
                    lean_ctor_set(v___x_1333_, 2, v_v_1432_);
                    lean_ctor_set(v___x_1333_, 1, v_k_1431_);
                    lean_ctor_set(v___x_1333_, 0, v___x_1436_);
                    v___x_1442_ = v___x_1333_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1436_);
                    lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_k_1431_);
                    lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_v_1432_);
                    lean_ctor_set(v_reuseFailAlloc_1443_, 3, v___x_1438_);
                    lean_ctor_set(v_reuseFailAlloc_1443_, 4, v___x_1440_);
                    v___x_1442_ = v_reuseFailAlloc_1443_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1442_;
            }
            18 => {
                v___x_1459_ = lean_unsigned_to_nat(3);
                if v_isShared_1458_ == 0 {
                    lean_ctor_set(v___x_1457_, 4, v_l_1424_);
                    lean_ctor_set(v___x_1457_, 2, v_v_1329_);
                    lean_ctor_set(v___x_1457_, 1, v_k_1328_);
                    lean_ctor_set(v___x_1457_, 0, v___x_1340_);
                    v___x_1461_ = v___x_1457_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1340_);
                    lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_k_1328_);
                    lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_v_1329_);
                    lean_ctor_set(v_reuseFailAlloc_1465_, 3, v_l_1424_);
                    lean_ctor_set(v_reuseFailAlloc_1465_, 4, v_l_1424_);
                    v___x_1461_ = v_reuseFailAlloc_1465_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1334_ == 0 {
                    lean_ctor_set(v___x_1333_, 4, v_r_1453_);
                    lean_ctor_set(v___x_1333_, 3, v___x_1461_);
                    lean_ctor_set(v___x_1333_, 2, v_v_1455_);
                    lean_ctor_set(v___x_1333_, 1, v_k_1454_);
                    lean_ctor_set(v___x_1333_, 0, v___x_1459_);
                    v___x_1463_ = v___x_1333_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1459_);
                    lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_k_1454_);
                    lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_v_1455_);
                    lean_ctor_set(v_reuseFailAlloc_1464_, 3, v___x_1461_);
                    lean_ctor_set(v_reuseFailAlloc_1464_, 4, v_r_1453_);
                    v___x_1463_ = v_reuseFailAlloc_1464_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1463_;
            }
            21 => {
                return v___x_1472_;
            }
            22 => {
                return v___x_1476_;
            }
            23 => {
                return v___x_1492_;
            }
            24 => {
                v_size_1497_ = lean_ctor_get(v_l_1484_, 0);
                v_size_1498_ = lean_ctor_get(v_r_1485_, 0);
                v_k_1499_ = lean_ctor_get(v_r_1485_, 1);
                v_v_1500_ = lean_ctor_get(v_r_1485_, 2);
                v_l_1501_ = lean_ctor_get(v_r_1485_, 3);
                v_r_1502_ = lean_ctor_get(v_r_1485_, 4);
                v___x_1503_ = lean_unsigned_to_nat(2);
                v___x_1504_ = lean_nat_mul(v___x_1503_, v_size_1497_);
                v___x_1505_ = lean_nat_dec_lt(v_size_1498_, v___x_1504_);
                lean_dec(v___x_1504_);
                if v___x_1505_ == 0 {
                    lean_inc(v_r_1502_);
                    lean_inc(v_l_1501_);
                    lean_inc(v_v_1500_);
                    lean_inc(v_k_1499_);
                    v_isSharedCheck_1534_ = (!lean_is_exclusive(v_r_1485_)) as u8;
                    if v_isSharedCheck_1534_ == 0 {
                        v_unused_1535_ = lean_ctor_get(v_r_1485_, 4);
                        lean_dec(v_unused_1535_);
                        v_unused_1536_ = lean_ctor_get(v_r_1485_, 3);
                        lean_dec(v_unused_1536_);
                        v_unused_1537_ = lean_ctor_get(v_r_1485_, 2);
                        lean_dec(v_unused_1537_);
                        v_unused_1538_ = lean_ctor_get(v_r_1485_, 1);
                        lean_dec(v_unused_1538_);
                        v_unused_1539_ = lean_ctor_get(v_r_1485_, 0);
                        lean_dec(v_unused_1539_);
                        v___x_1507_ = v_r_1485_;
                        v_isShared_1508_ = v_isSharedCheck_1534_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_r_1485_);
                        v___x_1507_ = lean_box(0);
                        v_isShared_1508_ = v_isSharedCheck_1534_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1333_);
                    v___x_1540_ = lean_nat_add(v___x_1479_, v_size_1481_);
                    lean_dec(v_size_1481_);
                    v___x_1541_ = lean_nat_add(v___x_1540_, v_size_1480_);
                    lean_dec(v___x_1540_);
                    v___x_1542_ = lean_nat_add(v___x_1479_, v_size_1480_);
                    v___x_1543_ = lean_nat_add(v___x_1542_, v_size_1498_);
                    lean_dec(v___x_1542_);
                    lean_inc_ref(v_r_1331_);
                    if v_isShared_1496_ == 0 {
                        lean_ctor_set(v___x_1495_, 4, v_r_1331_);
                        lean_ctor_set(v___x_1495_, 3, v_r_1485_);
                        lean_ctor_set(v___x_1495_, 2, v_v_1329_);
                        lean_ctor_set(v___x_1495_, 1, v_k_1328_);
                        lean_ctor_set(v___x_1495_, 0, v___x_1543_);
                        v___x_1545_ = v___x_1495_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1543_);
                        lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1328_);
                        lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1329_);
                        lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_r_1485_);
                        lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_r_1331_);
                        v___x_1545_ = v_reuseFailAlloc_1558_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1509_ = lean_nat_add(v___x_1479_, v_size_1481_);
                lean_dec(v_size_1481_);
                v___x_1510_ = lean_nat_add(v___x_1509_, v_size_1480_);
                lean_dec(v___x_1509_);
                v___x_1522_ = lean_nat_add(v___x_1479_, v_size_1497_);
                if lean_obj_tag(v_l_1501_) == 0 {
                    v_size_1532_ = lean_ctor_get(v_l_1501_, 0);
                    lean_inc(v_size_1532_);
                    v___y_1524_ = v_size_1532_;
                    state = 29;
                    continue;
                } else {
                    v___x_1533_ = lean_unsigned_to_nat(0);
                    v___y_1524_ = v___x_1533_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_1515_ = lean_nat_add(v___y_1513_, v___y_1514_);
                lean_dec(v___y_1514_);
                lean_dec(v___y_1513_);
                if v_isShared_1508_ == 0 {
                    lean_ctor_set(v___x_1507_, 4, v_r_1331_);
                    lean_ctor_set(v___x_1507_, 3, v_r_1502_);
                    lean_ctor_set(v___x_1507_, 2, v_v_1329_);
                    lean_ctor_set(v___x_1507_, 1, v_k_1328_);
                    lean_ctor_set(v___x_1507_, 0, v___x_1515_);
                    v___x_1517_ = v___x_1507_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1515_);
                    lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_k_1328_);
                    lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_v_1329_);
                    lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_r_1502_);
                    lean_ctor_set(v_reuseFailAlloc_1521_, 4, v_r_1331_);
                    v___x_1517_ = v_reuseFailAlloc_1521_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1496_ == 0 {
                    lean_ctor_set(v___x_1495_, 4, v___x_1517_);
                    lean_ctor_set(v___x_1495_, 3, v___y_1512_);
                    lean_ctor_set(v___x_1495_, 2, v_v_1500_);
                    lean_ctor_set(v___x_1495_, 1, v_k_1499_);
                    lean_ctor_set(v___x_1495_, 0, v___x_1510_);
                    v___x_1519_ = v___x_1495_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1510_);
                    lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_k_1499_);
                    lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_v_1500_);
                    lean_ctor_set(v_reuseFailAlloc_1520_, 3, v___y_1512_);
                    lean_ctor_set(v_reuseFailAlloc_1520_, 4, v___x_1517_);
                    v___x_1519_ = v_reuseFailAlloc_1520_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1519_;
            }
            29 => {
                v___x_1525_ = lean_nat_add(v___x_1522_, v___y_1524_);
                lean_dec(v___y_1524_);
                lean_dec(v___x_1522_);
                if v_isShared_1334_ == 0 {
                    lean_ctor_set(v___x_1333_, 4, v_l_1501_);
                    lean_ctor_set(v___x_1333_, 3, v_l_1484_);
                    lean_ctor_set(v___x_1333_, 2, v_v_1483_);
                    lean_ctor_set(v___x_1333_, 1, v_k_1482_);
                    lean_ctor_set(v___x_1333_, 0, v___x_1525_);
                    v___x_1527_ = v___x_1333_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1525_);
                    lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_k_1482_);
                    lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_v_1483_);
                    lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_l_1484_);
                    lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_l_1501_);
                    v___x_1527_ = v_reuseFailAlloc_1531_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1528_ = lean_nat_add(v___x_1479_, v_size_1480_);
                if lean_obj_tag(v_r_1502_) == 0 {
                    v_size_1529_ = lean_ctor_get(v_r_1502_, 0);
                    lean_inc(v_size_1529_);
                    v___y_1512_ = v___x_1527_;
                    v___y_1513_ = v___x_1528_;
                    v___y_1514_ = v_size_1529_;
                    state = 26;
                    continue;
                } else {
                    v___x_1530_ = lean_unsigned_to_nat(0);
                    v___y_1512_ = v___x_1527_;
                    v___y_1513_ = v___x_1528_;
                    v___y_1514_ = v___x_1530_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_1552_ = (!lean_is_exclusive(v_r_1331_)) as u8;
                if v_isSharedCheck_1552_ == 0 {
                    v_unused_1553_ = lean_ctor_get(v_r_1331_, 4);
                    lean_dec(v_unused_1553_);
                    v_unused_1554_ = lean_ctor_get(v_r_1331_, 3);
                    lean_dec(v_unused_1554_);
                    v_unused_1555_ = lean_ctor_get(v_r_1331_, 2);
                    lean_dec(v_unused_1555_);
                    v_unused_1556_ = lean_ctor_get(v_r_1331_, 1);
                    lean_dec(v_unused_1556_);
                    v_unused_1557_ = lean_ctor_get(v_r_1331_, 0);
                    lean_dec(v_unused_1557_);
                    v___x_1547_ = v_r_1331_;
                    v_isShared_1548_ = v_isSharedCheck_1552_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_r_1331_);
                    v___x_1547_ = lean_box(0);
                    v_isShared_1548_ = v_isSharedCheck_1552_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1548_ == 0 {
                    lean_ctor_set(v___x_1547_, 4, v___x_1545_);
                    lean_ctor_set(v___x_1547_, 3, v_l_1484_);
                    lean_ctor_set(v___x_1547_, 2, v_v_1483_);
                    lean_ctor_set(v___x_1547_, 1, v_k_1482_);
                    lean_ctor_set(v___x_1547_, 0, v___x_1541_);
                    v___x_1550_ = v___x_1547_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1541_);
                    lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_k_1482_);
                    lean_ctor_set(v_reuseFailAlloc_1551_, 2, v_v_1483_);
                    lean_ctor_set(v_reuseFailAlloc_1551_, 3, v_l_1484_);
                    lean_ctor_set(v_reuseFailAlloc_1551_, 4, v___x_1545_);
                    v___x_1550_ = v_reuseFailAlloc_1551_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1550_;
            }
            34 => {
                v___x_1572_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_1566_);
                if v_isShared_1571_ == 0 {
                    lean_ctor_set(v___x_1570_, 3, v_r_1566_);
                    lean_ctor_set(v___x_1570_, 2, v_v_1329_);
                    lean_ctor_set(v___x_1570_, 1, v_k_1328_);
                    lean_ctor_set(v___x_1570_, 0, v___x_1479_);
                    v___x_1574_ = v___x_1570_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1479_);
                    lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_k_1328_);
                    lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_v_1329_);
                    lean_ctor_set(v_reuseFailAlloc_1578_, 3, v_r_1566_);
                    lean_ctor_set(v_reuseFailAlloc_1578_, 4, v_r_1566_);
                    v___x_1574_ = v_reuseFailAlloc_1578_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_1334_ == 0 {
                    lean_ctor_set(v___x_1333_, 4, v___x_1574_);
                    lean_ctor_set(v___x_1333_, 3, v_l_1565_);
                    lean_ctor_set(v___x_1333_, 2, v_v_1568_);
                    lean_ctor_set(v___x_1333_, 1, v_k_1567_);
                    lean_ctor_set(v___x_1333_, 0, v___x_1572_);
                    v___x_1576_ = v___x_1333_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1572_);
                    lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_k_1567_);
                    lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_v_1568_);
                    lean_ctor_set(v_reuseFailAlloc_1577_, 3, v_l_1565_);
                    lean_ctor_set(v_reuseFailAlloc_1577_, 4, v___x_1574_);
                    v___x_1576_ = v_reuseFailAlloc_1577_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_1576_;
            }
            37 => {
                v_k_1588_ = lean_ctor_get(v_r_1582_, 1);
                v_v_1589_ = lean_ctor_get(v_r_1582_, 2);
                v_isSharedCheck_1603_ = (!lean_is_exclusive(v_r_1582_)) as u8;
                if v_isSharedCheck_1603_ == 0 {
                    v_unused_1604_ = lean_ctor_get(v_r_1582_, 4);
                    lean_dec(v_unused_1604_);
                    v_unused_1605_ = lean_ctor_get(v_r_1582_, 3);
                    lean_dec(v_unused_1605_);
                    v_unused_1606_ = lean_ctor_get(v_r_1582_, 0);
                    lean_dec(v_unused_1606_);
                    v___x_1591_ = v_r_1582_;
                    v_isShared_1592_ = v_isSharedCheck_1603_;
                    state = 38;
                    continue;
                } else {
                    lean_inc(v_v_1589_);
                    lean_inc(v_k_1588_);
                    lean_dec(v_r_1582_);
                    v___x_1591_ = lean_box(0);
                    v_isShared_1592_ = v_isSharedCheck_1603_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_1593_ = lean_unsigned_to_nat(3);
                if v_isShared_1592_ == 0 {
                    lean_ctor_set(v___x_1591_, 4, v_l_1565_);
                    lean_ctor_set(v___x_1591_, 3, v_l_1565_);
                    lean_ctor_set(v___x_1591_, 2, v_v_1584_);
                    lean_ctor_set(v___x_1591_, 1, v_k_1583_);
                    lean_ctor_set(v___x_1591_, 0, v___x_1479_);
                    v___x_1595_ = v___x_1591_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1479_);
                    lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_k_1583_);
                    lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_v_1584_);
                    lean_ctor_set(v_reuseFailAlloc_1602_, 3, v_l_1565_);
                    lean_ctor_set(v_reuseFailAlloc_1602_, 4, v_l_1565_);
                    v___x_1595_ = v_reuseFailAlloc_1602_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_1587_ == 0 {
                    lean_ctor_set(v___x_1586_, 4, v_l_1565_);
                    lean_ctor_set(v___x_1586_, 2, v_v_1329_);
                    lean_ctor_set(v___x_1586_, 1, v_k_1328_);
                    lean_ctor_set(v___x_1586_, 0, v___x_1479_);
                    v___x_1597_ = v___x_1586_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1479_);
                    lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_k_1328_);
                    lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_v_1329_);
                    lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_l_1565_);
                    lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_l_1565_);
                    v___x_1597_ = v_reuseFailAlloc_1601_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1334_ == 0 {
                    lean_ctor_set(v___x_1333_, 4, v___x_1597_);
                    lean_ctor_set(v___x_1333_, 3, v___x_1595_);
                    lean_ctor_set(v___x_1333_, 2, v_v_1589_);
                    lean_ctor_set(v___x_1333_, 1, v_k_1588_);
                    lean_ctor_set(v___x_1333_, 0, v___x_1593_);
                    v___x_1599_ = v___x_1333_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1593_);
                    lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_k_1588_);
                    lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_v_1589_);
                    lean_ctor_set(v_reuseFailAlloc_1600_, 3, v___x_1595_);
                    lean_ctor_set(v_reuseFailAlloc_1600_, 4, v___x_1597_);
                    v___x_1599_ = v_reuseFailAlloc_1600_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_1599_;
            }
            42 => {
                return v___x_1613_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg___boxed(
    mut v_k_1619_: *mut LeanObject,
    mut v_v_1620_: *mut LeanObject,
    mut v_t_1621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_boxed_1622_: u64 = 0;
    let mut v_res_1623_: *mut LeanObject = core::ptr::null_mut();
    v_k_boxed_1622_ = lean_unbox_uint64(v_k_1619_);
    lean_dec_ref(v_k_1619_);
    v_res_1623_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(
            v_k_boxed_1622_,
            v_v_1620_,
            v_t_1621_,
        );
    return v_res_1623_;
}
pub unsafe fn l_Std_CancellationContext_new() -> *mut LeanObject {
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: u64 = 0;
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: u64 = 0;
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_Std_CancellationToken_new();
    v___x_1628_ = lean_box(1);
    v___x_1629_ = 0u64;
    v___x_1630_ = l_Std_CancellationContext_new___closed__0;
    lean_inc_ref(v___x_1627_);
    v___x_1631_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1631_, 0, v___x_1627_);
    lean_ctor_set(v___x_1631_, 1, v___x_1630_);
    v___x_1632_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(
            v___x_1629_,
            v___x_1631_,
            v___x_1628_,
        );
    v___x_1633_ = 1u64;
    v___x_1634_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_1634_, 0, v___x_1632_);
    lean_ctor_set_uint64(
        v___x_1634_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1633_,
    );
    v___x_1635_ = l_Std_Mutex_new___redArg(v___x_1634_);
    v___x_1636_ = lean_alloc_ctor(0, 2, (8) as u32);
    lean_ctor_set(v___x_1636_, 0, v___x_1635_);
    lean_ctor_set(v___x_1636_, 1, v___x_1627_);
    lean_ctor_set_uint64(
        v___x_1636_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_1629_,
    );
    return v___x_1636_;
}
pub unsafe fn l_Std_CancellationContext_new___boxed(
    mut v_a_1637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1638_: *mut LeanObject = core::ptr::null_mut();
    v_res_1638_ = l_Std_CancellationContext_new();
    return v_res_1638_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(
    mut v_00_u03b2_1639_: *mut LeanObject,
    mut v_k_1640_: u64,
    mut v_v_1641_: *mut LeanObject,
    mut v_t_1642_: *mut LeanObject,
    mut v_hl_1643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    v___x_1644_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(
            v_k_1640_, v_v_1641_, v_t_1642_,
        );
    return v___x_1644_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___boxed(
    mut v_00_u03b2_1645_: *mut LeanObject,
    mut v_k_1646_: *mut LeanObject,
    mut v_v_1647_: *mut LeanObject,
    mut v_t_1648_: *mut LeanObject,
    mut v_hl_1649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_boxed_1650_: u64 = 0;
    let mut v_res_1651_: *mut LeanObject = core::ptr::null_mut();
    v_k_boxed_1650_ = lean_unbox_uint64(v_k_1646_);
    lean_dec_ref(v_k_1646_);
    v_res_1651_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(
        v_00_u03b2_1645_,
        v_k_boxed_1650_,
        v_v_1647_,
        v_t_1648_,
        v_hl_1649_,
    );
    return v_res_1651_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(
    mut v_mutex_1652_: *mut LeanObject,
    mut v_k_1653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1655_ = lean_ctor_get(v_mutex_1652_, 0);
    lean_inc(v_ref_1655_);
    v_mutex_1656_ = lean_ctor_get(v_mutex_1652_, 1);
    lean_inc(v_mutex_1656_);
    lean_dec_ref(v_mutex_1652_);
    v___x_1657_ = lean_io_basemutex_lock(v_mutex_1656_);
    v___x_1658_ = lean_apply_2(v_k_1653_, v_ref_1655_, lean_box(0));
    v___x_1659_ = lean_io_basemutex_unlock(v_mutex_1656_);
    lean_dec(v_mutex_1656_);
    return v___x_1658_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg___boxed(
    mut v_mutex_1660_: *mut LeanObject,
    mut v_k_1661_: *mut LeanObject,
    mut v___y_1662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1663_: *mut LeanObject = core::ptr::null_mut();
    v_res_1663_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(
        v_mutex_1660_,
        v_k_1661_,
    );
    return v_res_1663_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(
    mut v_00_u03b1_1664_: *mut LeanObject,
    mut v_00_u03b2_1665_: *mut LeanObject,
    mut v_mutex_1666_: *mut LeanObject,
    mut v_k_1667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    v___x_1669_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(
        v_mutex_1666_,
        v_k_1667_,
    );
    return v___x_1669_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___boxed(
    mut v_00_u03b1_1670_: *mut LeanObject,
    mut v_00_u03b2_1671_: *mut LeanObject,
    mut v_mutex_1672_: *mut LeanObject,
    mut v_k_1673_: *mut LeanObject,
    mut v___y_1674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1675_: *mut LeanObject = core::ptr::null_mut();
    v_res_1675_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(
        v_00_u03b1_1670_,
        v_00_u03b2_1671_,
        v_mutex_1672_,
        v_k_1673_,
    );
    return v_res_1675_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(
    mut v_x_1676_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_x_1676_);
    return v_x_1676_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0___boxed(
    mut v_x_1677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1678_: *mut LeanObject = core::ptr::null_mut();
    v_res_1678_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(v_x_1677_);
    lean_dec_ref(v_x_1677_);
    return v_res_1678_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(
    mut v___x_1679_: u64,
    mut v_x_1680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    v___x_1681_ = lean_box_uint64(v___x_1679_);
    v___x_1682_ = lean_array_push(v_x_1680_, v___x_1681_);
    return v___x_1682_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed(
    mut v___x_1683_: *mut LeanObject,
    mut v_x_1684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1350__boxed_1685_: u64 = 0;
    let mut v_res_1686_: *mut LeanObject = core::ptr::null_mut();
    v___x_1350__boxed_1685_ = lean_unbox_uint64(v___x_1683_);
    lean_dec_ref(v___x_1683_);
    v_res_1686_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(v___x_1350__boxed_1685_, v_x_1684_);
    return v_res_1686_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(
    mut v___x_1688_: u64,
    mut v_k_1689_: u64,
    mut v_t_1690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1698_: u8 = 0;
    let mut v___x_1699_: u64 = 0;
    let mut v___x_1700_: u8 = 0;
    let mut v___x_1701_: u64 = 0;
    let mut v___x_1702_: u8 = 0;
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1690_) == 0 {
                    v_size_1691_ = lean_ctor_get(v_t_1690_, 0);
                    v_k_1692_ = lean_ctor_get(v_t_1690_, 1);
                    v_v_1693_ = lean_ctor_get(v_t_1690_, 2);
                    v_l_1694_ = lean_ctor_get(v_t_1690_, 3);
                    v_r_1695_ = lean_ctor_get(v_t_1690_, 4);
                    v_isSharedCheck_1719_ = (!lean_is_exclusive(v_t_1690_)) as u8;
                    if v_isSharedCheck_1719_ == 0 {
                        v___x_1697_ = v_t_1690_;
                        v_isShared_1698_ = v_isSharedCheck_1719_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_1695_);
                        lean_inc(v_l_1694_);
                        lean_inc(v_v_1693_);
                        lean_inc(v_k_1692_);
                        lean_inc(v_size_1691_);
                        lean_dec(v_t_1690_);
                        v___x_1697_ = lean_box(0);
                        v_isShared_1698_ = v_isSharedCheck_1719_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_t_1690_;
                }
            }
            1 => {
                v___x_1699_ = lean_unbox_uint64(v_k_1692_);
                v___x_1700_ = lean_uint64_dec_lt(v_k_1689_, v___x_1699_);
                if v___x_1700_ == 0 {
                    v___x_1701_ = lean_unbox_uint64(v_k_1692_);
                    v___x_1702_ = lean_uint64_dec_eq(v_k_1689_, v___x_1701_);
                    if v___x_1702_ == 0 {
                        v___x_1703_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v___x_1688_, v_k_1689_, v_r_1695_);
                        if v_isShared_1698_ == 0 {
                            lean_ctor_set(v___x_1697_, 4, v___x_1703_);
                            v___x_1705_ = v___x_1697_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_size_1691_);
                            lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_k_1692_);
                            lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_v_1693_);
                            lean_ctor_set(v_reuseFailAlloc_1706_, 3, v_l_1694_);
                            lean_ctor_set(v_reuseFailAlloc_1706_, 4, v___x_1703_);
                            v___x_1705_ = v_reuseFailAlloc_1706_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_k_1692_);
                        v___f_1707_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0;
                        v___x_1708_ = lean_box_uint64(v___x_1688_);
                        v___f_1709_ = lean_alloc_closure(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                        lean_closure_set(v___f_1709_, 0, v___x_1708_);
                        v___x_1710_ = l_Prod_map___redArg(v___f_1707_, v___f_1709_, v_v_1693_);
                        v___x_1711_ = lean_box_uint64(v_k_1689_);
                        if v_isShared_1698_ == 0 {
                            lean_ctor_set(v___x_1697_, 2, v___x_1710_);
                            lean_ctor_set(v___x_1697_, 1, v___x_1711_);
                            v___x_1713_ = v___x_1697_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_size_1691_);
                            lean_ctor_set(v_reuseFailAlloc_1714_, 1, v___x_1711_);
                            lean_ctor_set(v_reuseFailAlloc_1714_, 2, v___x_1710_);
                            lean_ctor_set(v_reuseFailAlloc_1714_, 3, v_l_1694_);
                            lean_ctor_set(v_reuseFailAlloc_1714_, 4, v_r_1695_);
                            v___x_1713_ = v_reuseFailAlloc_1714_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_1715_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v___x_1688_, v_k_1689_, v_l_1694_);
                    if v_isShared_1698_ == 0 {
                        lean_ctor_set(v___x_1697_, 3, v___x_1715_);
                        v___x_1717_ = v___x_1697_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_size_1691_);
                        lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_k_1692_);
                        lean_ctor_set(v_reuseFailAlloc_1718_, 2, v_v_1693_);
                        lean_ctor_set(v_reuseFailAlloc_1718_, 3, v___x_1715_);
                        lean_ctor_set(v_reuseFailAlloc_1718_, 4, v_r_1695_);
                        v___x_1717_ = v_reuseFailAlloc_1718_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1705_;
            }
            3 => {
                return v___x_1713_;
            }
            4 => {
                return v___x_1717_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___boxed(
    mut v___x_1720_: *mut LeanObject,
    mut v_k_1721_: *mut LeanObject,
    mut v_t_1722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1362__boxed_1723_: u64 = 0;
    let mut v_k_boxed_1724_: u64 = 0;
    let mut v_res_1725_: *mut LeanObject = core::ptr::null_mut();
    v___x_1362__boxed_1723_ = lean_unbox_uint64(v___x_1720_);
    lean_dec_ref(v___x_1720_);
    v_k_boxed_1724_ = lean_unbox_uint64(v_k_1721_);
    lean_dec_ref(v_k_1721_);
    v_res_1725_ =
        l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(
            v___x_1362__boxed_1723_,
            v_k_boxed_1724_,
            v_t_1722_,
        );
    return v_res_1725_;
}
pub unsafe fn l_Std_CancellationContext_fork___lam__0(
    mut v_token_1726_: *mut LeanObject,
    mut v_id_1727_: u64,
    mut v_state_1728_: *mut LeanObject,
    mut v_root_1729_: *mut LeanObject,
    mut v___y_1730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1732_: u8 = 0;
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tokens_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_1736_: u64 = 0;
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: u64 = 0;
    let mut v___x_1745_: u64 = 0;
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1732_ = l_Std_CancellationToken_isCancelled(v_token_1726_);
                if v___x_1732_ == 0 {
                    v___x_1733_ = l_Std_CancellationToken_new();
                    v___x_1734_ = lean_st_ref_get(v___y_1730_);
                    v_tokens_1735_ = lean_ctor_get(v___x_1734_, 0);
                    v_id_1736_ = lean_ctor_get_uint64(
                        v___x_1734_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_isSharedCheck_1751_ = (!lean_is_exclusive(v___x_1734_)) as u8;
                    if v_isSharedCheck_1751_ == 0 {
                        v___x_1738_ = v___x_1734_;
                        v_isShared_1739_ = v_isSharedCheck_1751_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tokens_1735_);
                        lean_dec(v___x_1734_);
                        v___x_1738_ = lean_box(0);
                        v_isShared_1739_ = v_isSharedCheck_1751_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_state_1728_);
                    lean_inc_ref(v_root_1729_);
                    return v_root_1729_;
                }
            }
            1 => {
                v___x_1740_ = l_Std_CancellationContext_new___closed__0;
                lean_inc_ref(v___x_1733_);
                v___x_1741_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1741_, 0, v___x_1733_);
                lean_ctor_set(v___x_1741_, 1, v___x_1740_);
                v___x_1742_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_id_1736_, v___x_1741_, v_tokens_1735_);
                v___x_1743_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v_id_1736_, v_id_1727_, v___x_1742_);
                v___x_1744_ = 1u64;
                v___x_1745_ = lean_uint64_add(v_id_1736_, v___x_1744_);
                if v_isShared_1739_ == 0 {
                    lean_ctor_set(v___x_1738_, 0, v___x_1743_);
                    v___x_1747_ = v___x_1738_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1743_);
                    v___x_1747_ = v_reuseFailAlloc_1750_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint64(
                    v___x_1747_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1745_,
                );
                v___x_1748_ = lean_st_ref_set(v___y_1730_, v___x_1747_);
                v___x_1749_ = lean_alloc_ctor(0, 2, (8) as u32);
                lean_ctor_set(v___x_1749_, 0, v_state_1728_);
                lean_ctor_set(v___x_1749_, 1, v___x_1733_);
                lean_ctor_set_uint64(
                    v___x_1749_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_id_1736_,
                );
                return v___x_1749_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CancellationContext_fork___lam__0___boxed(
    mut v_token_1752_: *mut LeanObject,
    mut v_id_1753_: *mut LeanObject,
    mut v_state_1754_: *mut LeanObject,
    mut v_root_1755_: *mut LeanObject,
    mut v___y_1756_: *mut LeanObject,
    mut v___y_1757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_boxed_1758_: u64 = 0;
    let mut v_res_1759_: *mut LeanObject = core::ptr::null_mut();
    v_id_boxed_1758_ = lean_unbox_uint64(v_id_1753_);
    lean_dec_ref(v_id_1753_);
    v_res_1759_ = l_Std_CancellationContext_fork___lam__0(
        v_token_1752_,
        v_id_boxed_1758_,
        v_state_1754_,
        v_root_1755_,
        v___y_1756_,
    );
    lean_dec(v___y_1756_);
    lean_dec_ref(v_root_1755_);
    return v_res_1759_;
}
pub unsafe fn l_Std_CancellationContext_fork(mut v_root_1760_: *mut LeanObject) -> *mut LeanObject {
    let mut v_state_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_token_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_1764_: u64 = 0;
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    v_state_1762_ = lean_ctor_get(v_root_1760_, 0);
    lean_inc_ref_n(v_state_1762_, 2);
    v_token_1763_ = lean_ctor_get(v_root_1760_, 1);
    lean_inc_ref(v_token_1763_);
    v_id_1764_ = lean_ctor_get_uint64(
        v_root_1760_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    v___x_1765_ = lean_box_uint64(v_id_1764_);
    v___f_1766_ = lean_alloc_closure(
        l_Std_CancellationContext_fork___lam__0___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___f_1766_, 0, v_token_1763_);
    lean_closure_set(v___f_1766_, 1, v___x_1765_);
    lean_closure_set(v___f_1766_, 2, v_state_1762_);
    lean_closure_set(v___f_1766_, 3, v_root_1760_);
    v___x_1767_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(
        v_state_1762_,
        v___f_1766_,
    );
    return v___x_1767_;
}
pub unsafe fn l_Std_CancellationContext_fork___boxed(
    mut v_root_1768_: *mut LeanObject,
    mut v_a_1769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1770_: *mut LeanObject = core::ptr::null_mut();
    v_res_1770_ = l_Std_CancellationContext_fork(v_root_1768_);
    return v_res_1770_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(
    mut v_k_1771_: u64,
    mut v_t_1772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1779_: u8 = 0;
    let mut v___x_1780_: u64 = 0;
    let mut v___x_1781_: u8 = 0;
    let mut v___x_1782_: u64 = 0;
    let mut v___x_1783_: u8 = 0;
    let mut v_impl_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: u8 = 0;
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1802_: u8 = 0;
    let mut v_size_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1814_: u8 = 0;
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1840_: u8 = 0;
    let mut v_unused_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1854_: u8 = 0;
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut v_unused_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1865_: u8 = 0;
    let mut v_unused_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1883_: u8 = 0;
    let mut v_size_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1893_: u8 = 0;
    let mut v_unused_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1900_: u8 = 0;
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1908_: u8 = 0;
    let mut v_unused_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v_k_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1933_: u8 = 0;
    let mut v_unused_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1937_: u8 = 0;
    let mut v_unused_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1962_: u8 = 0;
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: u8 = 0;
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v_size_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: u8 = 0;
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1990_: u8 = 0;
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2015_: u8 = 0;
    let mut v_unused_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2030_: u8 = 0;
    let mut v_unused_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v_k_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2056_: u8 = 0;
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2067_: u8 = 0;
    let mut v_unused_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2089_: u8 = 0;
    let mut v_unused_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2095_: u8 = 0;
    let mut v_unused_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2103_: u8 = 0;
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: u8 = 0;
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2119_: u8 = 0;
    let mut v_size_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: u8 = 0;
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2131_: u8 = 0;
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2143_: u8 = 0;
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2147_: u8 = 0;
    let mut v_unused_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2166_: u8 = 0;
    let mut v_unused_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2182_: u8 = 0;
    let mut v_unused_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2190_: u8 = 0;
    let mut v_k_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2211_: u8 = 0;
    let mut v_unused_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2219_: u8 = 0;
    let mut v_k_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2226_: u8 = 0;
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut v_unused_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut v_unused_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2253_: u8 = 0;
    let mut v_unused_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: u8 = 0;
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2277_: u8 = 0;
    let mut v_size_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: u8 = 0;
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2289_: u8 = 0;
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2314_: u8 = 0;
    let mut v_unused_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2327_: u8 = 0;
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2331_: u8 = 0;
    let mut v_unused_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2338_: u8 = 0;
    let mut v_unused_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v_size_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2366_: u8 = 0;
    let mut v_unused_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2373_: u8 = 0;
    let mut v_k_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2378_: u8 = 0;
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2389_: u8 = 0;
    let mut v_unused_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2393_: u8 = 0;
    let mut v_unused_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2402_: u8 = 0;
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2410_: u8 = 0;
    let mut v_unused_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2419_: u8 = 0;
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut v_unused_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2433_: u8 = 0;
    let mut v_unused_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1772_) == 0 {
                    v_k_1773_ = lean_ctor_get(v_t_1772_, 1);
                    v_v_1774_ = lean_ctor_get(v_t_1772_, 2);
                    v_l_1775_ = lean_ctor_get(v_t_1772_, 3);
                    v_r_1776_ = lean_ctor_get(v_t_1772_, 4);
                    v_isSharedCheck_2433_ = (!lean_is_exclusive(v_t_1772_)) as u8;
                    if v_isSharedCheck_2433_ == 0 {
                        v_unused_2434_ = lean_ctor_get(v_t_1772_, 0);
                        lean_dec(v_unused_2434_);
                        v___x_1778_ = v_t_1772_;
                        v_isShared_1779_ = v_isSharedCheck_2433_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_1776_);
                        lean_inc(v_l_1775_);
                        lean_inc(v_v_1774_);
                        lean_inc(v_k_1773_);
                        lean_dec(v_t_1772_);
                        v___x_1778_ = lean_box(0);
                        v_isShared_1779_ = v_isSharedCheck_2433_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_t_1772_;
                }
            }
            1 => {
                v___x_1780_ = lean_unbox_uint64(v_k_1773_);
                v___x_1781_ = lean_uint64_dec_lt(v_k_1771_, v___x_1780_);
                if v___x_1781_ == 0 {
                    v___x_1782_ = lean_unbox_uint64(v_k_1773_);
                    v___x_1783_ = lean_uint64_dec_eq(v_k_1771_, v___x_1782_);
                    if v___x_1783_ == 0 {
                        v_impl_1784_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_1771_, v_r_1776_);
                        v___x_1785_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_impl_1784_) == 0 {
                            if lean_obj_tag(v_l_1775_) == 0 {
                                v_size_1786_ = lean_ctor_get(v_impl_1784_, 0);
                                lean_inc(v_size_1786_);
                                v_size_1787_ = lean_ctor_get(v_l_1775_, 0);
                                v_k_1788_ = lean_ctor_get(v_l_1775_, 1);
                                v_v_1789_ = lean_ctor_get(v_l_1775_, 2);
                                v_l_1790_ = lean_ctor_get(v_l_1775_, 3);
                                v_r_1791_ = lean_ctor_get(v_l_1775_, 4);
                                lean_inc(v_r_1791_);
                                v___x_1792_ = lean_unsigned_to_nat(3);
                                v___x_1793_ = lean_nat_mul(v___x_1792_, v_size_1786_);
                                v___x_1794_ = lean_nat_dec_lt(v___x_1793_, v_size_1787_);
                                lean_dec(v___x_1793_);
                                if v___x_1794_ == 0 {
                                    lean_dec(v_r_1791_);
                                    v___x_1795_ = lean_nat_add(v___x_1785_, v_size_1787_);
                                    v___x_1796_ = lean_nat_add(v___x_1795_, v_size_1786_);
                                    lean_dec(v_size_1786_);
                                    lean_dec(v___x_1795_);
                                    if v_isShared_1779_ == 0 {
                                        lean_ctor_set(v___x_1778_, 4, v_impl_1784_);
                                        lean_ctor_set(v___x_1778_, 0, v___x_1796_);
                                        v___x_1798_ = v___x_1778_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
                                        lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_k_1773_);
                                        lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_v_1774_);
                                        lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_l_1775_);
                                        lean_ctor_set(v_reuseFailAlloc_1799_, 4, v_impl_1784_);
                                        v___x_1798_ = v_reuseFailAlloc_1799_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_inc(v_l_1790_);
                                    lean_inc(v_v_1789_);
                                    lean_inc(v_k_1788_);
                                    lean_inc(v_size_1787_);
                                    v_isSharedCheck_1865_ = (!lean_is_exclusive(v_l_1775_)) as u8;
                                    if v_isSharedCheck_1865_ == 0 {
                                        v_unused_1866_ = lean_ctor_get(v_l_1775_, 4);
                                        lean_dec(v_unused_1866_);
                                        v_unused_1867_ = lean_ctor_get(v_l_1775_, 3);
                                        lean_dec(v_unused_1867_);
                                        v_unused_1868_ = lean_ctor_get(v_l_1775_, 2);
                                        lean_dec(v_unused_1868_);
                                        v_unused_1869_ = lean_ctor_get(v_l_1775_, 1);
                                        lean_dec(v_unused_1869_);
                                        v_unused_1870_ = lean_ctor_get(v_l_1775_, 0);
                                        lean_dec(v_unused_1870_);
                                        v___x_1801_ = v_l_1775_;
                                        v_isShared_1802_ = v_isSharedCheck_1865_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_dec(v_l_1775_);
                                        v___x_1801_ = lean_box(0);
                                        v_isShared_1802_ = v_isSharedCheck_1865_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_1871_ = lean_ctor_get(v_impl_1784_, 0);
                                lean_inc(v_size_1871_);
                                v___x_1872_ = lean_nat_add(v___x_1785_, v_size_1871_);
                                lean_dec(v_size_1871_);
                                if v_isShared_1779_ == 0 {
                                    lean_ctor_set(v___x_1778_, 4, v_impl_1784_);
                                    lean_ctor_set(v___x_1778_, 0, v___x_1872_);
                                    v___x_1874_ = v___x_1778_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
                                    lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_k_1773_);
                                    lean_ctor_set(v_reuseFailAlloc_1875_, 2, v_v_1774_);
                                    lean_ctor_set(v_reuseFailAlloc_1875_, 3, v_l_1775_);
                                    lean_ctor_set(v_reuseFailAlloc_1875_, 4, v_impl_1784_);
                                    v___x_1874_ = v_reuseFailAlloc_1875_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if lean_obj_tag(v_l_1775_) == 0 {
                                v_l_1876_ = lean_ctor_get(v_l_1775_, 3);
                                if lean_obj_tag(v_l_1876_) == 0 {
                                    lean_inc_ref(v_l_1876_);
                                    v_r_1877_ = lean_ctor_get(v_l_1775_, 4);
                                    lean_inc(v_r_1877_);
                                    if lean_obj_tag(v_r_1877_) == 0 {
                                        v_size_1878_ = lean_ctor_get(v_l_1775_, 0);
                                        v_k_1879_ = lean_ctor_get(v_l_1775_, 1);
                                        v_v_1880_ = lean_ctor_get(v_l_1775_, 2);
                                        v_isSharedCheck_1893_ =
                                            (!lean_is_exclusive(v_l_1775_)) as u8;
                                        if v_isSharedCheck_1893_ == 0 {
                                            v_unused_1894_ = lean_ctor_get(v_l_1775_, 4);
                                            lean_dec(v_unused_1894_);
                                            v_unused_1895_ = lean_ctor_get(v_l_1775_, 3);
                                            lean_dec(v_unused_1895_);
                                            v___x_1882_ = v_l_1775_;
                                            v_isShared_1883_ = v_isSharedCheck_1893_;
                                            state = 14;
                                            continue;
                                        } else {
                                            lean_inc(v_v_1880_);
                                            lean_inc(v_k_1879_);
                                            lean_inc(v_size_1878_);
                                            lean_dec(v_l_1775_);
                                            v___x_1882_ = lean_box(0);
                                            v_isShared_1883_ = v_isSharedCheck_1893_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_1896_ = lean_ctor_get(v_l_1775_, 1);
                                        v_v_1897_ = lean_ctor_get(v_l_1775_, 2);
                                        v_isSharedCheck_1908_ =
                                            (!lean_is_exclusive(v_l_1775_)) as u8;
                                        if v_isSharedCheck_1908_ == 0 {
                                            v_unused_1909_ = lean_ctor_get(v_l_1775_, 4);
                                            lean_dec(v_unused_1909_);
                                            v_unused_1910_ = lean_ctor_get(v_l_1775_, 3);
                                            lean_dec(v_unused_1910_);
                                            v_unused_1911_ = lean_ctor_get(v_l_1775_, 0);
                                            lean_dec(v_unused_1911_);
                                            v___x_1899_ = v_l_1775_;
                                            v_isShared_1900_ = v_isSharedCheck_1908_;
                                            state = 17;
                                            continue;
                                        } else {
                                            lean_inc(v_v_1897_);
                                            lean_inc(v_k_1896_);
                                            lean_dec(v_l_1775_);
                                            v___x_1899_ = lean_box(0);
                                            v_isShared_1900_ = v_isSharedCheck_1908_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_1912_ = lean_ctor_get(v_l_1775_, 4);
                                    lean_inc(v_r_1912_);
                                    if lean_obj_tag(v_r_1912_) == 0 {
                                        lean_inc(v_l_1876_);
                                        v_k_1913_ = lean_ctor_get(v_l_1775_, 1);
                                        v_v_1914_ = lean_ctor_get(v_l_1775_, 2);
                                        v_isSharedCheck_1937_ =
                                            (!lean_is_exclusive(v_l_1775_)) as u8;
                                        if v_isSharedCheck_1937_ == 0 {
                                            v_unused_1938_ = lean_ctor_get(v_l_1775_, 4);
                                            lean_dec(v_unused_1938_);
                                            v_unused_1939_ = lean_ctor_get(v_l_1775_, 3);
                                            lean_dec(v_unused_1939_);
                                            v_unused_1940_ = lean_ctor_get(v_l_1775_, 0);
                                            lean_dec(v_unused_1940_);
                                            v___x_1916_ = v_l_1775_;
                                            v_isShared_1917_ = v_isSharedCheck_1937_;
                                            state = 20;
                                            continue;
                                        } else {
                                            lean_inc(v_v_1914_);
                                            lean_inc(v_k_1913_);
                                            lean_dec(v_l_1775_);
                                            v___x_1916_ = lean_box(0);
                                            v_isShared_1917_ = v_isSharedCheck_1937_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_1941_ = lean_unsigned_to_nat(2);
                                        if v_isShared_1779_ == 0 {
                                            lean_ctor_set(v___x_1778_, 4, v_r_1912_);
                                            lean_ctor_set(v___x_1778_, 0, v___x_1941_);
                                            v___x_1943_ = v___x_1778_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_1944_ =
                                                lean_alloc_ctor(0, 5, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1941_);
                                            lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_k_1773_);
                                            lean_ctor_set(v_reuseFailAlloc_1944_, 2, v_v_1774_);
                                            lean_ctor_set(v_reuseFailAlloc_1944_, 3, v_l_1775_);
                                            lean_ctor_set(v_reuseFailAlloc_1944_, 4, v_r_1912_);
                                            v___x_1943_ = v_reuseFailAlloc_1944_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_1779_ == 0 {
                                    lean_ctor_set(v___x_1778_, 4, v_l_1775_);
                                    lean_ctor_set(v___x_1778_, 0, v___x_1785_);
                                    v___x_1946_ = v___x_1778_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1785_);
                                    lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_k_1773_);
                                    lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_v_1774_);
                                    lean_ctor_set(v_reuseFailAlloc_1947_, 3, v_l_1775_);
                                    lean_ctor_set(v_reuseFailAlloc_1947_, 4, v_l_1775_);
                                    v___x_1946_ = v_reuseFailAlloc_1947_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_1778_);
                        lean_dec(v_v_1774_);
                        lean_dec(v_k_1773_);
                        if lean_obj_tag(v_l_1775_) == 0 {
                            if lean_obj_tag(v_r_1776_) == 0 {
                                v_size_1948_ = lean_ctor_get(v_l_1775_, 0);
                                v_k_1949_ = lean_ctor_get(v_l_1775_, 1);
                                v_v_1950_ = lean_ctor_get(v_l_1775_, 2);
                                v_l_1951_ = lean_ctor_get(v_l_1775_, 3);
                                v_r_1952_ = lean_ctor_get(v_l_1775_, 4);
                                lean_inc(v_r_1952_);
                                v_size_1953_ = lean_ctor_get(v_r_1776_, 0);
                                v_k_1954_ = lean_ctor_get(v_r_1776_, 1);
                                v_v_1955_ = lean_ctor_get(v_r_1776_, 2);
                                v_l_1956_ = lean_ctor_get(v_r_1776_, 3);
                                lean_inc(v_l_1956_);
                                v_r_1957_ = lean_ctor_get(v_r_1776_, 4);
                                v___x_1958_ = lean_unsigned_to_nat(1);
                                v___x_1959_ = lean_nat_dec_lt(v_size_1948_, v_size_1953_);
                                if v___x_1959_ == 0 {
                                    lean_inc(v_l_1951_);
                                    lean_inc(v_v_1950_);
                                    lean_inc(v_k_1949_);
                                    v_isSharedCheck_2095_ = (!lean_is_exclusive(v_l_1775_)) as u8;
                                    if v_isSharedCheck_2095_ == 0 {
                                        v_unused_2096_ = lean_ctor_get(v_l_1775_, 4);
                                        lean_dec(v_unused_2096_);
                                        v_unused_2097_ = lean_ctor_get(v_l_1775_, 3);
                                        lean_dec(v_unused_2097_);
                                        v_unused_2098_ = lean_ctor_get(v_l_1775_, 2);
                                        lean_dec(v_unused_2098_);
                                        v_unused_2099_ = lean_ctor_get(v_l_1775_, 1);
                                        lean_dec(v_unused_2099_);
                                        v_unused_2100_ = lean_ctor_get(v_l_1775_, 0);
                                        lean_dec(v_unused_2100_);
                                        v___x_1961_ = v_l_1775_;
                                        v_isShared_1962_ = v_isSharedCheck_2095_;
                                        state = 27;
                                        continue;
                                    } else {
                                        lean_dec(v_l_1775_);
                                        v___x_1961_ = lean_box(0);
                                        v_isShared_1962_ = v_isSharedCheck_2095_;
                                        state = 27;
                                        continue;
                                    }
                                } else {
                                    lean_inc(v_r_1957_);
                                    lean_inc(v_v_1955_);
                                    lean_inc(v_k_1954_);
                                    v_isSharedCheck_2253_ = (!lean_is_exclusive(v_r_1776_)) as u8;
                                    if v_isSharedCheck_2253_ == 0 {
                                        v_unused_2254_ = lean_ctor_get(v_r_1776_, 4);
                                        lean_dec(v_unused_2254_);
                                        v_unused_2255_ = lean_ctor_get(v_r_1776_, 3);
                                        lean_dec(v_unused_2255_);
                                        v_unused_2256_ = lean_ctor_get(v_r_1776_, 2);
                                        lean_dec(v_unused_2256_);
                                        v_unused_2257_ = lean_ctor_get(v_r_1776_, 1);
                                        lean_dec(v_unused_2257_);
                                        v_unused_2258_ = lean_ctor_get(v_r_1776_, 0);
                                        lean_dec(v_unused_2258_);
                                        v___x_2102_ = v_r_1776_;
                                        v_isShared_2103_ = v_isSharedCheck_2253_;
                                        state = 49;
                                        continue;
                                    } else {
                                        lean_dec(v_r_1776_);
                                        v___x_2102_ = lean_box(0);
                                        v_isShared_2103_ = v_isSharedCheck_2253_;
                                        state = 49;
                                        continue;
                                    }
                                }
                            } else {
                                return v_l_1775_;
                            }
                        } else {
                            return v_r_1776_;
                        }
                    }
                } else {
                    v_impl_2259_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_1771_, v_l_1775_);
                    v___x_2260_ = lean_unsigned_to_nat(1);
                    if lean_obj_tag(v_impl_2259_) == 0 {
                        if lean_obj_tag(v_r_1776_) == 0 {
                            v_size_2261_ = lean_ctor_get(v_impl_2259_, 0);
                            lean_inc(v_size_2261_);
                            v_size_2262_ = lean_ctor_get(v_r_1776_, 0);
                            v_k_2263_ = lean_ctor_get(v_r_1776_, 1);
                            v_v_2264_ = lean_ctor_get(v_r_1776_, 2);
                            v_l_2265_ = lean_ctor_get(v_r_1776_, 3);
                            lean_inc(v_l_2265_);
                            v_r_2266_ = lean_ctor_get(v_r_1776_, 4);
                            v___x_2267_ = lean_unsigned_to_nat(3);
                            v___x_2268_ = lean_nat_mul(v___x_2267_, v_size_2261_);
                            v___x_2269_ = lean_nat_dec_lt(v___x_2268_, v_size_2262_);
                            lean_dec(v___x_2268_);
                            if v___x_2269_ == 0 {
                                lean_dec(v_l_2265_);
                                v___x_2270_ = lean_nat_add(v___x_2260_, v_size_2261_);
                                lean_dec(v_size_2261_);
                                v___x_2271_ = lean_nat_add(v___x_2270_, v_size_2262_);
                                lean_dec(v___x_2270_);
                                if v_isShared_1779_ == 0 {
                                    lean_ctor_set(v___x_1778_, 3, v_impl_2259_);
                                    lean_ctor_set(v___x_1778_, 0, v___x_2271_);
                                    v___x_2273_ = v___x_1778_;
                                    state = 72;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
                                    lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_k_1773_);
                                    lean_ctor_set(v_reuseFailAlloc_2274_, 2, v_v_1774_);
                                    lean_ctor_set(v_reuseFailAlloc_2274_, 3, v_impl_2259_);
                                    lean_ctor_set(v_reuseFailAlloc_2274_, 4, v_r_1776_);
                                    v___x_2273_ = v_reuseFailAlloc_2274_;
                                    state = 72;
                                    continue;
                                }
                            } else {
                                lean_inc(v_r_2266_);
                                lean_inc(v_v_2264_);
                                lean_inc(v_k_2263_);
                                lean_inc(v_size_2262_);
                                v_isSharedCheck_2338_ = (!lean_is_exclusive(v_r_1776_)) as u8;
                                if v_isSharedCheck_2338_ == 0 {
                                    v_unused_2339_ = lean_ctor_get(v_r_1776_, 4);
                                    lean_dec(v_unused_2339_);
                                    v_unused_2340_ = lean_ctor_get(v_r_1776_, 3);
                                    lean_dec(v_unused_2340_);
                                    v_unused_2341_ = lean_ctor_get(v_r_1776_, 2);
                                    lean_dec(v_unused_2341_);
                                    v_unused_2342_ = lean_ctor_get(v_r_1776_, 1);
                                    lean_dec(v_unused_2342_);
                                    v_unused_2343_ = lean_ctor_get(v_r_1776_, 0);
                                    lean_dec(v_unused_2343_);
                                    v___x_2276_ = v_r_1776_;
                                    v_isShared_2277_ = v_isSharedCheck_2338_;
                                    state = 73;
                                    continue;
                                } else {
                                    lean_dec(v_r_1776_);
                                    v___x_2276_ = lean_box(0);
                                    v_isShared_2277_ = v_isSharedCheck_2338_;
                                    state = 73;
                                    continue;
                                }
                            }
                        } else {
                            v_size_2344_ = lean_ctor_get(v_impl_2259_, 0);
                            lean_inc(v_size_2344_);
                            v___x_2345_ = lean_nat_add(v___x_2260_, v_size_2344_);
                            lean_dec(v_size_2344_);
                            if v_isShared_1779_ == 0 {
                                lean_ctor_set(v___x_1778_, 3, v_impl_2259_);
                                lean_ctor_set(v___x_1778_, 0, v___x_2345_);
                                v___x_2347_ = v___x_1778_;
                                state = 83;
                                continue;
                            } else {
                                v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
                                lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_k_1773_);
                                lean_ctor_set(v_reuseFailAlloc_2348_, 2, v_v_1774_);
                                lean_ctor_set(v_reuseFailAlloc_2348_, 3, v_impl_2259_);
                                lean_ctor_set(v_reuseFailAlloc_2348_, 4, v_r_1776_);
                                v___x_2347_ = v_reuseFailAlloc_2348_;
                                state = 83;
                                continue;
                            }
                        }
                    } else {
                        if lean_obj_tag(v_r_1776_) == 0 {
                            v_l_2349_ = lean_ctor_get(v_r_1776_, 3);
                            lean_inc(v_l_2349_);
                            if lean_obj_tag(v_l_2349_) == 0 {
                                v_r_2350_ = lean_ctor_get(v_r_1776_, 4);
                                lean_inc(v_r_2350_);
                                if lean_obj_tag(v_r_2350_) == 0 {
                                    v_size_2351_ = lean_ctor_get(v_r_1776_, 0);
                                    v_k_2352_ = lean_ctor_get(v_r_1776_, 1);
                                    v_v_2353_ = lean_ctor_get(v_r_1776_, 2);
                                    v_isSharedCheck_2366_ = (!lean_is_exclusive(v_r_1776_)) as u8;
                                    if v_isSharedCheck_2366_ == 0 {
                                        v_unused_2367_ = lean_ctor_get(v_r_1776_, 4);
                                        lean_dec(v_unused_2367_);
                                        v_unused_2368_ = lean_ctor_get(v_r_1776_, 3);
                                        lean_dec(v_unused_2368_);
                                        v___x_2355_ = v_r_1776_;
                                        v_isShared_2356_ = v_isSharedCheck_2366_;
                                        state = 84;
                                        continue;
                                    } else {
                                        lean_inc(v_v_2353_);
                                        lean_inc(v_k_2352_);
                                        lean_inc(v_size_2351_);
                                        lean_dec(v_r_1776_);
                                        v___x_2355_ = lean_box(0);
                                        v_isShared_2356_ = v_isSharedCheck_2366_;
                                        state = 84;
                                        continue;
                                    }
                                } else {
                                    v_k_2369_ = lean_ctor_get(v_r_1776_, 1);
                                    v_v_2370_ = lean_ctor_get(v_r_1776_, 2);
                                    v_isSharedCheck_2393_ = (!lean_is_exclusive(v_r_1776_)) as u8;
                                    if v_isSharedCheck_2393_ == 0 {
                                        v_unused_2394_ = lean_ctor_get(v_r_1776_, 4);
                                        lean_dec(v_unused_2394_);
                                        v_unused_2395_ = lean_ctor_get(v_r_1776_, 3);
                                        lean_dec(v_unused_2395_);
                                        v_unused_2396_ = lean_ctor_get(v_r_1776_, 0);
                                        lean_dec(v_unused_2396_);
                                        v___x_2372_ = v_r_1776_;
                                        v_isShared_2373_ = v_isSharedCheck_2393_;
                                        state = 87;
                                        continue;
                                    } else {
                                        lean_inc(v_v_2370_);
                                        lean_inc(v_k_2369_);
                                        lean_dec(v_r_1776_);
                                        v___x_2372_ = lean_box(0);
                                        v_isShared_2373_ = v_isSharedCheck_2393_;
                                        state = 87;
                                        continue;
                                    }
                                }
                            } else {
                                v_r_2397_ = lean_ctor_get(v_r_1776_, 4);
                                lean_inc(v_r_2397_);
                                if lean_obj_tag(v_r_2397_) == 0 {
                                    v_k_2398_ = lean_ctor_get(v_r_1776_, 1);
                                    v_v_2399_ = lean_ctor_get(v_r_1776_, 2);
                                    v_isSharedCheck_2410_ = (!lean_is_exclusive(v_r_1776_)) as u8;
                                    if v_isSharedCheck_2410_ == 0 {
                                        v_unused_2411_ = lean_ctor_get(v_r_1776_, 4);
                                        lean_dec(v_unused_2411_);
                                        v_unused_2412_ = lean_ctor_get(v_r_1776_, 3);
                                        lean_dec(v_unused_2412_);
                                        v_unused_2413_ = lean_ctor_get(v_r_1776_, 0);
                                        lean_dec(v_unused_2413_);
                                        v___x_2401_ = v_r_1776_;
                                        v_isShared_2402_ = v_isSharedCheck_2410_;
                                        state = 92;
                                        continue;
                                    } else {
                                        lean_inc(v_v_2399_);
                                        lean_inc(v_k_2398_);
                                        lean_dec(v_r_1776_);
                                        v___x_2401_ = lean_box(0);
                                        v_isShared_2402_ = v_isSharedCheck_2410_;
                                        state = 92;
                                        continue;
                                    }
                                } else {
                                    v_size_2414_ = lean_ctor_get(v_r_1776_, 0);
                                    v_k_2415_ = lean_ctor_get(v_r_1776_, 1);
                                    v_v_2416_ = lean_ctor_get(v_r_1776_, 2);
                                    v_isSharedCheck_2427_ = (!lean_is_exclusive(v_r_1776_)) as u8;
                                    if v_isSharedCheck_2427_ == 0 {
                                        v_unused_2428_ = lean_ctor_get(v_r_1776_, 4);
                                        lean_dec(v_unused_2428_);
                                        v_unused_2429_ = lean_ctor_get(v_r_1776_, 3);
                                        lean_dec(v_unused_2429_);
                                        v___x_2418_ = v_r_1776_;
                                        v_isShared_2419_ = v_isSharedCheck_2427_;
                                        state = 95;
                                        continue;
                                    } else {
                                        lean_inc(v_v_2416_);
                                        lean_inc(v_k_2415_);
                                        lean_inc(v_size_2414_);
                                        lean_dec(v_r_1776_);
                                        v___x_2418_ = lean_box(0);
                                        v_isShared_2419_ = v_isSharedCheck_2427_;
                                        state = 95;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            if v_isShared_1779_ == 0 {
                                lean_ctor_set(v___x_1778_, 3, v_r_1776_);
                                lean_ctor_set(v___x_1778_, 0, v___x_2260_);
                                v___x_2431_ = v___x_1778_;
                                state = 98;
                                continue;
                            } else {
                                v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2260_);
                                lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_k_1773_);
                                lean_ctor_set(v_reuseFailAlloc_2432_, 2, v_v_1774_);
                                lean_ctor_set(v_reuseFailAlloc_2432_, 3, v_r_1776_);
                                lean_ctor_set(v_reuseFailAlloc_2432_, 4, v_r_1776_);
                                v___x_2431_ = v_reuseFailAlloc_2432_;
                                state = 98;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1798_;
            }
            3 => {
                v_size_1803_ = lean_ctor_get(v_l_1790_, 0);
                v_size_1804_ = lean_ctor_get(v_r_1791_, 0);
                v_k_1805_ = lean_ctor_get(v_r_1791_, 1);
                v_v_1806_ = lean_ctor_get(v_r_1791_, 2);
                v_l_1807_ = lean_ctor_get(v_r_1791_, 3);
                v_r_1808_ = lean_ctor_get(v_r_1791_, 4);
                v___x_1809_ = lean_unsigned_to_nat(2);
                v___x_1810_ = lean_nat_mul(v___x_1809_, v_size_1803_);
                v___x_1811_ = lean_nat_dec_lt(v_size_1804_, v___x_1810_);
                lean_dec(v___x_1810_);
                if v___x_1811_ == 0 {
                    lean_inc(v_r_1808_);
                    lean_inc(v_l_1807_);
                    lean_inc(v_v_1806_);
                    lean_inc(v_k_1805_);
                    v_isSharedCheck_1840_ = (!lean_is_exclusive(v_r_1791_)) as u8;
                    if v_isSharedCheck_1840_ == 0 {
                        v_unused_1841_ = lean_ctor_get(v_r_1791_, 4);
                        lean_dec(v_unused_1841_);
                        v_unused_1842_ = lean_ctor_get(v_r_1791_, 3);
                        lean_dec(v_unused_1842_);
                        v_unused_1843_ = lean_ctor_get(v_r_1791_, 2);
                        lean_dec(v_unused_1843_);
                        v_unused_1844_ = lean_ctor_get(v_r_1791_, 1);
                        lean_dec(v_unused_1844_);
                        v_unused_1845_ = lean_ctor_get(v_r_1791_, 0);
                        lean_dec(v_unused_1845_);
                        v___x_1813_ = v_r_1791_;
                        v_isShared_1814_ = v_isSharedCheck_1840_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_r_1791_);
                        v___x_1813_ = lean_box(0);
                        v_isShared_1814_ = v_isSharedCheck_1840_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1778_);
                    v___x_1846_ = lean_nat_add(v___x_1785_, v_size_1787_);
                    lean_dec(v_size_1787_);
                    v___x_1847_ = lean_nat_add(v___x_1846_, v_size_1786_);
                    lean_dec(v___x_1846_);
                    v___x_1848_ = lean_nat_add(v___x_1785_, v_size_1786_);
                    lean_dec(v_size_1786_);
                    v___x_1849_ = lean_nat_add(v___x_1848_, v_size_1804_);
                    lean_dec(v___x_1848_);
                    lean_inc_ref(v_impl_1784_);
                    if v_isShared_1802_ == 0 {
                        lean_ctor_set(v___x_1801_, 4, v_impl_1784_);
                        lean_ctor_set(v___x_1801_, 3, v_r_1791_);
                        lean_ctor_set(v___x_1801_, 2, v_v_1774_);
                        lean_ctor_set(v___x_1801_, 1, v_k_1773_);
                        lean_ctor_set(v___x_1801_, 0, v___x_1849_);
                        v___x_1851_ = v___x_1801_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1849_);
                        lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_k_1773_);
                        lean_ctor_set(v_reuseFailAlloc_1864_, 2, v_v_1774_);
                        lean_ctor_set(v_reuseFailAlloc_1864_, 3, v_r_1791_);
                        lean_ctor_set(v_reuseFailAlloc_1864_, 4, v_impl_1784_);
                        v___x_1851_ = v_reuseFailAlloc_1864_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1815_ = lean_nat_add(v___x_1785_, v_size_1787_);
                lean_dec(v_size_1787_);
                v___x_1816_ = lean_nat_add(v___x_1815_, v_size_1786_);
                lean_dec(v___x_1815_);
                v___x_1828_ = lean_nat_add(v___x_1785_, v_size_1803_);
                if lean_obj_tag(v_l_1807_) == 0 {
                    v_size_1838_ = lean_ctor_get(v_l_1807_, 0);
                    lean_inc(v_size_1838_);
                    v___y_1830_ = v_size_1838_;
                    state = 8;
                    continue;
                } else {
                    v___x_1839_ = lean_unsigned_to_nat(0);
                    v___y_1830_ = v___x_1839_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1821_ = lean_nat_add(v___y_1818_, v___y_1820_);
                lean_dec(v___y_1820_);
                lean_dec(v___y_1818_);
                if v_isShared_1814_ == 0 {
                    lean_ctor_set(v___x_1813_, 4, v_impl_1784_);
                    lean_ctor_set(v___x_1813_, 3, v_r_1808_);
                    lean_ctor_set(v___x_1813_, 2, v_v_1774_);
                    lean_ctor_set(v___x_1813_, 1, v_k_1773_);
                    lean_ctor_set(v___x_1813_, 0, v___x_1821_);
                    v___x_1823_ = v___x_1813_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1821_);
                    lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_k_1773_);
                    lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_v_1774_);
                    lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_r_1808_);
                    lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_impl_1784_);
                    v___x_1823_ = v_reuseFailAlloc_1827_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1802_ == 0 {
                    lean_ctor_set(v___x_1801_, 4, v___x_1823_);
                    lean_ctor_set(v___x_1801_, 3, v___y_1819_);
                    lean_ctor_set(v___x_1801_, 2, v_v_1806_);
                    lean_ctor_set(v___x_1801_, 1, v_k_1805_);
                    lean_ctor_set(v___x_1801_, 0, v___x_1816_);
                    v___x_1825_ = v___x_1801_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1816_);
                    lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_k_1805_);
                    lean_ctor_set(v_reuseFailAlloc_1826_, 2, v_v_1806_);
                    lean_ctor_set(v_reuseFailAlloc_1826_, 3, v___y_1819_);
                    lean_ctor_set(v_reuseFailAlloc_1826_, 4, v___x_1823_);
                    v___x_1825_ = v_reuseFailAlloc_1826_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1825_;
            }
            8 => {
                v___x_1831_ = lean_nat_add(v___x_1828_, v___y_1830_);
                lean_dec(v___y_1830_);
                lean_dec(v___x_1828_);
                if v_isShared_1779_ == 0 {
                    lean_ctor_set(v___x_1778_, 4, v_l_1807_);
                    lean_ctor_set(v___x_1778_, 3, v_l_1790_);
                    lean_ctor_set(v___x_1778_, 2, v_v_1789_);
                    lean_ctor_set(v___x_1778_, 1, v_k_1788_);
                    lean_ctor_set(v___x_1778_, 0, v___x_1831_);
                    v___x_1833_ = v___x_1778_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1831_);
                    lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_k_1788_);
                    lean_ctor_set(v_reuseFailAlloc_1837_, 2, v_v_1789_);
                    lean_ctor_set(v_reuseFailAlloc_1837_, 3, v_l_1790_);
                    lean_ctor_set(v_reuseFailAlloc_1837_, 4, v_l_1807_);
                    v___x_1833_ = v_reuseFailAlloc_1837_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1834_ = lean_nat_add(v___x_1785_, v_size_1786_);
                lean_dec(v_size_1786_);
                if lean_obj_tag(v_r_1808_) == 0 {
                    v_size_1835_ = lean_ctor_get(v_r_1808_, 0);
                    lean_inc(v_size_1835_);
                    v___y_1818_ = v___x_1834_;
                    v___y_1819_ = v___x_1833_;
                    v___y_1820_ = v_size_1835_;
                    state = 5;
                    continue;
                } else {
                    v___x_1836_ = lean_unsigned_to_nat(0);
                    v___y_1818_ = v___x_1834_;
                    v___y_1819_ = v___x_1833_;
                    v___y_1820_ = v___x_1836_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1858_ = (!lean_is_exclusive(v_impl_1784_)) as u8;
                if v_isSharedCheck_1858_ == 0 {
                    v_unused_1859_ = lean_ctor_get(v_impl_1784_, 4);
                    lean_dec(v_unused_1859_);
                    v_unused_1860_ = lean_ctor_get(v_impl_1784_, 3);
                    lean_dec(v_unused_1860_);
                    v_unused_1861_ = lean_ctor_get(v_impl_1784_, 2);
                    lean_dec(v_unused_1861_);
                    v_unused_1862_ = lean_ctor_get(v_impl_1784_, 1);
                    lean_dec(v_unused_1862_);
                    v_unused_1863_ = lean_ctor_get(v_impl_1784_, 0);
                    lean_dec(v_unused_1863_);
                    v___x_1853_ = v_impl_1784_;
                    v_isShared_1854_ = v_isSharedCheck_1858_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_impl_1784_);
                    v___x_1853_ = lean_box(0);
                    v_isShared_1854_ = v_isSharedCheck_1858_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1854_ == 0 {
                    lean_ctor_set(v___x_1853_, 4, v___x_1851_);
                    lean_ctor_set(v___x_1853_, 3, v_l_1790_);
                    lean_ctor_set(v___x_1853_, 2, v_v_1789_);
                    lean_ctor_set(v___x_1853_, 1, v_k_1788_);
                    lean_ctor_set(v___x_1853_, 0, v___x_1847_);
                    v___x_1856_ = v___x_1853_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1847_);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_k_1788_);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_v_1789_);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_l_1790_);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 4, v___x_1851_);
                    v___x_1856_ = v_reuseFailAlloc_1857_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1856_;
            }
            13 => {
                return v___x_1874_;
            }
            14 => {
                v_size_1884_ = lean_ctor_get(v_r_1877_, 0);
                v___x_1885_ = lean_nat_add(v___x_1785_, v_size_1878_);
                lean_dec(v_size_1878_);
                v___x_1886_ = lean_nat_add(v___x_1785_, v_size_1884_);
                if v_isShared_1883_ == 0 {
                    lean_ctor_set(v___x_1882_, 4, v_impl_1784_);
                    lean_ctor_set(v___x_1882_, 3, v_r_1877_);
                    lean_ctor_set(v___x_1882_, 2, v_v_1774_);
                    lean_ctor_set(v___x_1882_, 1, v_k_1773_);
                    lean_ctor_set(v___x_1882_, 0, v___x_1886_);
                    v___x_1888_ = v___x_1882_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1886_);
                    lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_k_1773_);
                    lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_v_1774_);
                    lean_ctor_set(v_reuseFailAlloc_1892_, 3, v_r_1877_);
                    lean_ctor_set(v_reuseFailAlloc_1892_, 4, v_impl_1784_);
                    v___x_1888_ = v_reuseFailAlloc_1892_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1779_ == 0 {
                    lean_ctor_set(v___x_1778_, 4, v___x_1888_);
                    lean_ctor_set(v___x_1778_, 3, v_l_1876_);
                    lean_ctor_set(v___x_1778_, 2, v_v_1880_);
                    lean_ctor_set(v___x_1778_, 1, v_k_1879_);
                    lean_ctor_set(v___x_1778_, 0, v___x_1885_);
                    v___x_1890_ = v___x_1778_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1885_);
                    lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_k_1879_);
                    lean_ctor_set(v_reuseFailAlloc_1891_, 2, v_v_1880_);
                    lean_ctor_set(v_reuseFailAlloc_1891_, 3, v_l_1876_);
                    lean_ctor_set(v_reuseFailAlloc_1891_, 4, v___x_1888_);
                    v___x_1890_ = v_reuseFailAlloc_1891_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1890_;
            }
            17 => {
                v___x_1901_ = lean_unsigned_to_nat(3);
                if v_isShared_1900_ == 0 {
                    lean_ctor_set(v___x_1899_, 3, v_r_1877_);
                    lean_ctor_set(v___x_1899_, 2, v_v_1774_);
                    lean_ctor_set(v___x_1899_, 1, v_k_1773_);
                    lean_ctor_set(v___x_1899_, 0, v___x_1785_);
                    v___x_1903_ = v___x_1899_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1785_);
                    lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_k_1773_);
                    lean_ctor_set(v_reuseFailAlloc_1907_, 2, v_v_1774_);
                    lean_ctor_set(v_reuseFailAlloc_1907_, 3, v_r_1877_);
                    lean_ctor_set(v_reuseFailAlloc_1907_, 4, v_r_1877_);
                    v___x_1903_ = v_reuseFailAlloc_1907_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1779_ == 0 {
                    lean_ctor_set(v___x_1778_, 4, v___x_1903_);
                    lean_ctor_set(v___x_1778_, 3, v_l_1876_);
                    lean_ctor_set(v___x_1778_, 2, v_v_1897_);
                    lean_ctor_set(v___x_1778_, 1, v_k_1896_);
                    lean_ctor_set(v___x_1778_, 0, v___x_1901_);
                    v___x_1905_ = v___x_1778_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1901_);
                    lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_k_1896_);
                    lean_ctor_set(v_reuseFailAlloc_1906_, 2, v_v_1897_);
                    lean_ctor_set(v_reuseFailAlloc_1906_, 3, v_l_1876_);
                    lean_ctor_set(v_reuseFailAlloc_1906_, 4, v___x_1903_);
                    v___x_1905_ = v_reuseFailAlloc_1906_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1905_;
            }
            20 => {
                v_k_1918_ = lean_ctor_get(v_r_1912_, 1);
                v_v_1919_ = lean_ctor_get(v_r_1912_, 2);
                v_isSharedCheck_1933_ = (!lean_is_exclusive(v_r_1912_)) as u8;
                if v_isSharedCheck_1933_ == 0 {
                    v_unused_1934_ = lean_ctor_get(v_r_1912_, 4);
                    lean_dec(v_unused_1934_);
                    v_unused_1935_ = lean_ctor_get(v_r_1912_, 3);
                    lean_dec(v_unused_1935_);
                    v_unused_1936_ = lean_ctor_get(v_r_1912_, 0);
                    lean_dec(v_unused_1936_);
                    v___x_1921_ = v_r_1912_;
                    v_isShared_1922_ = v_isSharedCheck_1933_;
                    state = 21;
                    continue;
                } else {
                    lean_inc(v_v_1919_);
                    lean_inc(v_k_1918_);
                    lean_dec(v_r_1912_);
                    v___x_1921_ = lean_box(0);
                    v_isShared_1922_ = v_isSharedCheck_1933_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_1923_ = lean_unsigned_to_nat(3);
                if v_isShared_1922_ == 0 {
                    lean_ctor_set(v___x_1921_, 4, v_l_1876_);
                    lean_ctor_set(v___x_1921_, 3, v_l_1876_);
                    lean_ctor_set(v___x_1921_, 2, v_v_1914_);
                    lean_ctor_set(v___x_1921_, 1, v_k_1913_);
                    lean_ctor_set(v___x_1921_, 0, v___x_1785_);
                    v___x_1925_ = v___x_1921_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1785_);
                    lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_k_1913_);
                    lean_ctor_set(v_reuseFailAlloc_1932_, 2, v_v_1914_);
                    lean_ctor_set(v_reuseFailAlloc_1932_, 3, v_l_1876_);
                    lean_ctor_set(v_reuseFailAlloc_1932_, 4, v_l_1876_);
                    v___x_1925_ = v_reuseFailAlloc_1932_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_1917_ == 0 {
                    lean_ctor_set(v___x_1916_, 4, v_l_1876_);
                    lean_ctor_set(v___x_1916_, 2, v_v_1774_);
                    lean_ctor_set(v___x_1916_, 1, v_k_1773_);
                    lean_ctor_set(v___x_1916_, 0, v___x_1785_);
                    v___x_1927_ = v___x_1916_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1785_);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_k_1773_);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_v_1774_);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_l_1876_);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_l_1876_);
                    v___x_1927_ = v_reuseFailAlloc_1931_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_1779_ == 0 {
                    lean_ctor_set(v___x_1778_, 4, v___x_1927_);
                    lean_ctor_set(v___x_1778_, 3, v___x_1925_);
                    lean_ctor_set(v___x_1778_, 2, v_v_1919_);
                    lean_ctor_set(v___x_1778_, 1, v_k_1918_);
                    lean_ctor_set(v___x_1778_, 0, v___x_1923_);
                    v___x_1929_ = v___x_1778_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1923_);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_k_1918_);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_v_1919_);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 3, v___x_1925_);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 4, v___x_1927_);
                    v___x_1929_ = v_reuseFailAlloc_1930_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1929_;
            }
            25 => {
                return v___x_1943_;
            }
            26 => {
                return v___x_1946_;
            }
            27 => {
                v___x_1963_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(
                    v_k_1949_, v_v_1950_, v_l_1951_, v_r_1952_,
                );
                v_tree_1964_ = lean_ctor_get(v___x_1963_, 2);
                lean_inc(v_tree_1964_);
                if lean_obj_tag(v_tree_1964_) == 0 {
                    v_k_1965_ = lean_ctor_get(v___x_1963_, 0);
                    lean_inc(v_k_1965_);
                    v_v_1966_ = lean_ctor_get(v___x_1963_, 1);
                    lean_inc(v_v_1966_);
                    lean_dec_ref(v___x_1963_);
                    v_size_1967_ = lean_ctor_get(v_tree_1964_, 0);
                    v___x_1968_ = lean_unsigned_to_nat(3);
                    v___x_1969_ = lean_nat_mul(v___x_1968_, v_size_1967_);
                    v___x_1970_ = lean_nat_dec_lt(v___x_1969_, v_size_1953_);
                    lean_dec(v___x_1969_);
                    if v___x_1970_ == 0 {
                        lean_dec(v_l_1956_);
                        v___x_1971_ = lean_nat_add(v___x_1958_, v_size_1967_);
                        v___x_1972_ = lean_nat_add(v___x_1971_, v_size_1953_);
                        lean_dec(v___x_1971_);
                        if v_isShared_1962_ == 0 {
                            lean_ctor_set(v___x_1961_, 4, v_r_1776_);
                            lean_ctor_set(v___x_1961_, 3, v_tree_1964_);
                            lean_ctor_set(v___x_1961_, 2, v_v_1966_);
                            lean_ctor_set(v___x_1961_, 1, v_k_1965_);
                            lean_ctor_set(v___x_1961_, 0, v___x_1972_);
                            v___x_1974_ = v___x_1961_;
                            state = 28;
                            continue;
                        } else {
                            v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
                            lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_k_1965_);
                            lean_ctor_set(v_reuseFailAlloc_1975_, 2, v_v_1966_);
                            lean_ctor_set(v_reuseFailAlloc_1975_, 3, v_tree_1964_);
                            lean_ctor_set(v_reuseFailAlloc_1975_, 4, v_r_1776_);
                            v___x_1974_ = v_reuseFailAlloc_1975_;
                            state = 28;
                            continue;
                        }
                    } else {
                        lean_inc(v_r_1957_);
                        lean_inc(v_v_1955_);
                        lean_inc(v_k_1954_);
                        lean_inc(v_size_1953_);
                        v_isSharedCheck_2030_ = (!lean_is_exclusive(v_r_1776_)) as u8;
                        if v_isSharedCheck_2030_ == 0 {
                            v_unused_2031_ = lean_ctor_get(v_r_1776_, 4);
                            lean_dec(v_unused_2031_);
                            v_unused_2032_ = lean_ctor_get(v_r_1776_, 3);
                            lean_dec(v_unused_2032_);
                            v_unused_2033_ = lean_ctor_get(v_r_1776_, 2);
                            lean_dec(v_unused_2033_);
                            v_unused_2034_ = lean_ctor_get(v_r_1776_, 1);
                            lean_dec(v_unused_2034_);
                            v_unused_2035_ = lean_ctor_get(v_r_1776_, 0);
                            lean_dec(v_unused_2035_);
                            v___x_1977_ = v_r_1776_;
                            v_isShared_1978_ = v_isSharedCheck_2030_;
                            state = 29;
                            continue;
                        } else {
                            lean_dec(v_r_1776_);
                            v___x_1977_ = lean_box(0);
                            v_isShared_1978_ = v_isSharedCheck_2030_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_r_1957_);
                    lean_inc(v_v_1955_);
                    lean_inc(v_k_1954_);
                    lean_inc(v_size_1953_);
                    v_isSharedCheck_2089_ = (!lean_is_exclusive(v_r_1776_)) as u8;
                    if v_isSharedCheck_2089_ == 0 {
                        v_unused_2090_ = lean_ctor_get(v_r_1776_, 4);
                        lean_dec(v_unused_2090_);
                        v_unused_2091_ = lean_ctor_get(v_r_1776_, 3);
                        lean_dec(v_unused_2091_);
                        v_unused_2092_ = lean_ctor_get(v_r_1776_, 2);
                        lean_dec(v_unused_2092_);
                        v_unused_2093_ = lean_ctor_get(v_r_1776_, 1);
                        lean_dec(v_unused_2093_);
                        v_unused_2094_ = lean_ctor_get(v_r_1776_, 0);
                        lean_dec(v_unused_2094_);
                        v___x_2037_ = v_r_1776_;
                        v_isShared_2038_ = v_isSharedCheck_2089_;
                        state = 38;
                        continue;
                    } else {
                        lean_dec(v_r_1776_);
                        v___x_2037_ = lean_box(0);
                        v_isShared_2038_ = v_isSharedCheck_2089_;
                        state = 38;
                        continue;
                    }
                }
            }
            28 => {
                return v___x_1974_;
            }
            29 => {
                v_size_1979_ = lean_ctor_get(v_l_1956_, 0);
                v_k_1980_ = lean_ctor_get(v_l_1956_, 1);
                v_v_1981_ = lean_ctor_get(v_l_1956_, 2);
                v_l_1982_ = lean_ctor_get(v_l_1956_, 3);
                v_r_1983_ = lean_ctor_get(v_l_1956_, 4);
                v_size_1984_ = lean_ctor_get(v_r_1957_, 0);
                v___x_1985_ = lean_unsigned_to_nat(2);
                v___x_1986_ = lean_nat_mul(v___x_1985_, v_size_1984_);
                v___x_1987_ = lean_nat_dec_lt(v_size_1979_, v___x_1986_);
                lean_dec(v___x_1986_);
                if v___x_1987_ == 0 {
                    lean_inc(v_r_1983_);
                    lean_inc(v_l_1982_);
                    lean_inc(v_v_1981_);
                    lean_inc(v_k_1980_);
                    v_isSharedCheck_2015_ = (!lean_is_exclusive(v_l_1956_)) as u8;
                    if v_isSharedCheck_2015_ == 0 {
                        v_unused_2016_ = lean_ctor_get(v_l_1956_, 4);
                        lean_dec(v_unused_2016_);
                        v_unused_2017_ = lean_ctor_get(v_l_1956_, 3);
                        lean_dec(v_unused_2017_);
                        v_unused_2018_ = lean_ctor_get(v_l_1956_, 2);
                        lean_dec(v_unused_2018_);
                        v_unused_2019_ = lean_ctor_get(v_l_1956_, 1);
                        lean_dec(v_unused_2019_);
                        v_unused_2020_ = lean_ctor_get(v_l_1956_, 0);
                        lean_dec(v_unused_2020_);
                        v___x_1989_ = v_l_1956_;
                        v_isShared_1990_ = v_isSharedCheck_2015_;
                        state = 30;
                        continue;
                    } else {
                        lean_dec(v_l_1956_);
                        v___x_1989_ = lean_box(0);
                        v_isShared_1990_ = v_isSharedCheck_2015_;
                        state = 30;
                        continue;
                    }
                } else {
                    v___x_2021_ = lean_nat_add(v___x_1958_, v_size_1967_);
                    v___x_2022_ = lean_nat_add(v___x_2021_, v_size_1953_);
                    lean_dec(v_size_1953_);
                    v___x_2023_ = lean_nat_add(v___x_2021_, v_size_1979_);
                    lean_dec(v___x_2021_);
                    if v_isShared_1978_ == 0 {
                        lean_ctor_set(v___x_1977_, 4, v_l_1956_);
                        lean_ctor_set(v___x_1977_, 3, v_tree_1964_);
                        lean_ctor_set(v___x_1977_, 2, v_v_1966_);
                        lean_ctor_set(v___x_1977_, 1, v_k_1965_);
                        lean_ctor_set(v___x_1977_, 0, v___x_2023_);
                        v___x_2025_ = v___x_1977_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2023_);
                        lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_k_1965_);
                        lean_ctor_set(v_reuseFailAlloc_2029_, 2, v_v_1966_);
                        lean_ctor_set(v_reuseFailAlloc_2029_, 3, v_tree_1964_);
                        lean_ctor_set(v_reuseFailAlloc_2029_, 4, v_l_1956_);
                        v___x_2025_ = v_reuseFailAlloc_2029_;
                        state = 36;
                        continue;
                    }
                }
            }
            30 => {
                v___x_1991_ = lean_nat_add(v___x_1958_, v_size_1967_);
                v___x_1992_ = lean_nat_add(v___x_1991_, v_size_1953_);
                lean_dec(v_size_1953_);
                if lean_obj_tag(v_l_1982_) == 0 {
                    v_size_2013_ = lean_ctor_get(v_l_1982_, 0);
                    lean_inc(v_size_2013_);
                    v___y_2005_ = v_size_2013_;
                    state = 34;
                    continue;
                } else {
                    v___x_2014_ = lean_unsigned_to_nat(0);
                    v___y_2005_ = v___x_2014_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_1997_ = lean_nat_add(v___y_1995_, v___y_1996_);
                lean_dec(v___y_1996_);
                lean_dec(v___y_1995_);
                if v_isShared_1990_ == 0 {
                    lean_ctor_set(v___x_1989_, 4, v_r_1957_);
                    lean_ctor_set(v___x_1989_, 3, v_r_1983_);
                    lean_ctor_set(v___x_1989_, 2, v_v_1955_);
                    lean_ctor_set(v___x_1989_, 1, v_k_1954_);
                    lean_ctor_set(v___x_1989_, 0, v___x_1997_);
                    v___x_1999_ = v___x_1989_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1997_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_k_1954_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_v_1955_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_r_1983_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 4, v_r_1957_);
                    v___x_1999_ = v_reuseFailAlloc_2003_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1978_ == 0 {
                    lean_ctor_set(v___x_1977_, 4, v___x_1999_);
                    lean_ctor_set(v___x_1977_, 3, v___y_1994_);
                    lean_ctor_set(v___x_1977_, 2, v_v_1981_);
                    lean_ctor_set(v___x_1977_, 1, v_k_1980_);
                    lean_ctor_set(v___x_1977_, 0, v___x_1992_);
                    v___x_2001_ = v___x_1977_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1992_);
                    lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_k_1980_);
                    lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_v_1981_);
                    lean_ctor_set(v_reuseFailAlloc_2002_, 3, v___y_1994_);
                    lean_ctor_set(v_reuseFailAlloc_2002_, 4, v___x_1999_);
                    v___x_2001_ = v_reuseFailAlloc_2002_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2001_;
            }
            34 => {
                v___x_2006_ = lean_nat_add(v___x_1991_, v___y_2005_);
                lean_dec(v___y_2005_);
                lean_dec(v___x_1991_);
                if v_isShared_1962_ == 0 {
                    lean_ctor_set(v___x_1961_, 4, v_l_1982_);
                    lean_ctor_set(v___x_1961_, 3, v_tree_1964_);
                    lean_ctor_set(v___x_1961_, 2, v_v_1966_);
                    lean_ctor_set(v___x_1961_, 1, v_k_1965_);
                    lean_ctor_set(v___x_1961_, 0, v___x_2006_);
                    v___x_2008_ = v___x_1961_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2006_);
                    lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_k_1965_);
                    lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_v_1966_);
                    lean_ctor_set(v_reuseFailAlloc_2012_, 3, v_tree_1964_);
                    lean_ctor_set(v_reuseFailAlloc_2012_, 4, v_l_1982_);
                    v___x_2008_ = v_reuseFailAlloc_2012_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_2009_ = lean_nat_add(v___x_1958_, v_size_1984_);
                if lean_obj_tag(v_r_1983_) == 0 {
                    v_size_2010_ = lean_ctor_get(v_r_1983_, 0);
                    lean_inc(v_size_2010_);
                    v___y_1994_ = v___x_2008_;
                    v___y_1995_ = v___x_2009_;
                    v___y_1996_ = v_size_2010_;
                    state = 31;
                    continue;
                } else {
                    v___x_2011_ = lean_unsigned_to_nat(0);
                    v___y_1994_ = v___x_2008_;
                    v___y_1995_ = v___x_2009_;
                    v___y_1996_ = v___x_2011_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                if v_isShared_1962_ == 0 {
                    lean_ctor_set(v___x_1961_, 4, v_r_1957_);
                    lean_ctor_set(v___x_1961_, 3, v___x_2025_);
                    lean_ctor_set(v___x_1961_, 2, v_v_1955_);
                    lean_ctor_set(v___x_1961_, 1, v_k_1954_);
                    lean_ctor_set(v___x_1961_, 0, v___x_2022_);
                    v___x_2027_ = v___x_1961_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2022_);
                    lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_k_1954_);
                    lean_ctor_set(v_reuseFailAlloc_2028_, 2, v_v_1955_);
                    lean_ctor_set(v_reuseFailAlloc_2028_, 3, v___x_2025_);
                    lean_ctor_set(v_reuseFailAlloc_2028_, 4, v_r_1957_);
                    v___x_2027_ = v_reuseFailAlloc_2028_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_2027_;
            }
            38 => {
                if lean_obj_tag(v_l_1956_) == 0 {
                    if lean_obj_tag(v_r_1957_) == 0 {
                        v_k_2039_ = lean_ctor_get(v___x_1963_, 0);
                        lean_inc(v_k_2039_);
                        v_v_2040_ = lean_ctor_get(v___x_1963_, 1);
                        lean_inc(v_v_2040_);
                        lean_dec_ref(v___x_1963_);
                        v_size_2041_ = lean_ctor_get(v_l_1956_, 0);
                        v___x_2042_ = lean_nat_add(v___x_1958_, v_size_1953_);
                        lean_dec(v_size_1953_);
                        v___x_2043_ = lean_nat_add(v___x_1958_, v_size_2041_);
                        if v_isShared_2038_ == 0 {
                            lean_ctor_set(v___x_2037_, 4, v_l_1956_);
                            lean_ctor_set(v___x_2037_, 3, v_tree_1964_);
                            lean_ctor_set(v___x_2037_, 2, v_v_2040_);
                            lean_ctor_set(v___x_2037_, 1, v_k_2039_);
                            lean_ctor_set(v___x_2037_, 0, v___x_2043_);
                            v___x_2045_ = v___x_2037_;
                            state = 39;
                            continue;
                        } else {
                            v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2043_);
                            lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_k_2039_);
                            lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_v_2040_);
                            lean_ctor_set(v_reuseFailAlloc_2049_, 3, v_tree_1964_);
                            lean_ctor_set(v_reuseFailAlloc_2049_, 4, v_l_1956_);
                            v___x_2045_ = v_reuseFailAlloc_2049_;
                            state = 39;
                            continue;
                        }
                    } else {
                        lean_dec(v_size_1953_);
                        v_k_2050_ = lean_ctor_get(v___x_1963_, 0);
                        lean_inc(v_k_2050_);
                        v_v_2051_ = lean_ctor_get(v___x_1963_, 1);
                        lean_inc(v_v_2051_);
                        lean_dec_ref(v___x_1963_);
                        v_k_2052_ = lean_ctor_get(v_l_1956_, 1);
                        v_v_2053_ = lean_ctor_get(v_l_1956_, 2);
                        v_isSharedCheck_2067_ = (!lean_is_exclusive(v_l_1956_)) as u8;
                        if v_isSharedCheck_2067_ == 0 {
                            v_unused_2068_ = lean_ctor_get(v_l_1956_, 4);
                            lean_dec(v_unused_2068_);
                            v_unused_2069_ = lean_ctor_get(v_l_1956_, 3);
                            lean_dec(v_unused_2069_);
                            v_unused_2070_ = lean_ctor_get(v_l_1956_, 0);
                            lean_dec(v_unused_2070_);
                            v___x_2055_ = v_l_1956_;
                            v_isShared_2056_ = v_isSharedCheck_2067_;
                            state = 41;
                            continue;
                        } else {
                            lean_inc(v_v_2053_);
                            lean_inc(v_k_2052_);
                            lean_dec(v_l_1956_);
                            v___x_2055_ = lean_box(0);
                            v_isShared_2056_ = v_isSharedCheck_2067_;
                            state = 41;
                            continue;
                        }
                    }
                } else {
                    if lean_obj_tag(v_r_1957_) == 0 {
                        lean_dec(v_size_1953_);
                        v_k_2071_ = lean_ctor_get(v___x_1963_, 0);
                        lean_inc(v_k_2071_);
                        v_v_2072_ = lean_ctor_get(v___x_1963_, 1);
                        lean_inc(v_v_2072_);
                        lean_dec_ref(v___x_1963_);
                        v___x_2073_ = lean_unsigned_to_nat(3);
                        if v_isShared_2038_ == 0 {
                            lean_ctor_set(v___x_2037_, 4, v_l_1956_);
                            lean_ctor_set(v___x_2037_, 2, v_v_2072_);
                            lean_ctor_set(v___x_2037_, 1, v_k_2071_);
                            lean_ctor_set(v___x_2037_, 0, v___x_1958_);
                            v___x_2075_ = v___x_2037_;
                            state = 45;
                            continue;
                        } else {
                            v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_1958_);
                            lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_k_2071_);
                            lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_v_2072_);
                            lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_l_1956_);
                            lean_ctor_set(v_reuseFailAlloc_2079_, 4, v_l_1956_);
                            v___x_2075_ = v_reuseFailAlloc_2079_;
                            state = 45;
                            continue;
                        }
                    } else {
                        v_k_2080_ = lean_ctor_get(v___x_1963_, 0);
                        lean_inc(v_k_2080_);
                        v_v_2081_ = lean_ctor_get(v___x_1963_, 1);
                        lean_inc(v_v_2081_);
                        lean_dec_ref(v___x_1963_);
                        if v_isShared_2038_ == 0 {
                            lean_ctor_set(v___x_2037_, 3, v_r_1957_);
                            v___x_2083_ = v___x_2037_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_size_1953_);
                            lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_k_1954_);
                            lean_ctor_set(v_reuseFailAlloc_2088_, 2, v_v_1955_);
                            lean_ctor_set(v_reuseFailAlloc_2088_, 3, v_r_1957_);
                            lean_ctor_set(v_reuseFailAlloc_2088_, 4, v_r_1957_);
                            v___x_2083_ = v_reuseFailAlloc_2088_;
                            state = 47;
                            continue;
                        }
                    }
                }
            }
            39 => {
                if v_isShared_1962_ == 0 {
                    lean_ctor_set(v___x_1961_, 4, v_r_1957_);
                    lean_ctor_set(v___x_1961_, 3, v___x_2045_);
                    lean_ctor_set(v___x_1961_, 2, v_v_1955_);
                    lean_ctor_set(v___x_1961_, 1, v_k_1954_);
                    lean_ctor_set(v___x_1961_, 0, v___x_2042_);
                    v___x_2047_ = v___x_1961_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2042_);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_k_1954_);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_v_1955_);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 3, v___x_2045_);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 4, v_r_1957_);
                    v___x_2047_ = v_reuseFailAlloc_2048_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_2047_;
            }
            41 => {
                v___x_2057_ = lean_unsigned_to_nat(3);
                if v_isShared_2056_ == 0 {
                    lean_ctor_set(v___x_2055_, 4, v_r_1957_);
                    lean_ctor_set(v___x_2055_, 3, v_r_1957_);
                    lean_ctor_set(v___x_2055_, 2, v_v_2051_);
                    lean_ctor_set(v___x_2055_, 1, v_k_2050_);
                    lean_ctor_set(v___x_2055_, 0, v___x_1958_);
                    v___x_2059_ = v___x_2055_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_1958_);
                    lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_k_2050_);
                    lean_ctor_set(v_reuseFailAlloc_2066_, 2, v_v_2051_);
                    lean_ctor_set(v_reuseFailAlloc_2066_, 3, v_r_1957_);
                    lean_ctor_set(v_reuseFailAlloc_2066_, 4, v_r_1957_);
                    v___x_2059_ = v_reuseFailAlloc_2066_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                if v_isShared_2038_ == 0 {
                    lean_ctor_set(v___x_2037_, 3, v_r_1957_);
                    lean_ctor_set(v___x_2037_, 0, v___x_1958_);
                    v___x_2061_ = v___x_2037_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_1958_);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_k_1954_);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 2, v_v_1955_);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 3, v_r_1957_);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 4, v_r_1957_);
                    v___x_2061_ = v_reuseFailAlloc_2065_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                if v_isShared_1962_ == 0 {
                    lean_ctor_set(v___x_1961_, 4, v___x_2061_);
                    lean_ctor_set(v___x_1961_, 3, v___x_2059_);
                    lean_ctor_set(v___x_1961_, 2, v_v_2053_);
                    lean_ctor_set(v___x_1961_, 1, v_k_2052_);
                    lean_ctor_set(v___x_1961_, 0, v___x_2057_);
                    v___x_2063_ = v___x_1961_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2057_);
                    lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_k_2052_);
                    lean_ctor_set(v_reuseFailAlloc_2064_, 2, v_v_2053_);
                    lean_ctor_set(v_reuseFailAlloc_2064_, 3, v___x_2059_);
                    lean_ctor_set(v_reuseFailAlloc_2064_, 4, v___x_2061_);
                    v___x_2063_ = v_reuseFailAlloc_2064_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_2063_;
            }
            45 => {
                if v_isShared_1962_ == 0 {
                    lean_ctor_set(v___x_1961_, 4, v_r_1957_);
                    lean_ctor_set(v___x_1961_, 3, v___x_2075_);
                    lean_ctor_set(v___x_1961_, 2, v_v_1955_);
                    lean_ctor_set(v___x_1961_, 1, v_k_1954_);
                    lean_ctor_set(v___x_1961_, 0, v___x_2073_);
                    v___x_2077_ = v___x_1961_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2073_);
                    lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_k_1954_);
                    lean_ctor_set(v_reuseFailAlloc_2078_, 2, v_v_1955_);
                    lean_ctor_set(v_reuseFailAlloc_2078_, 3, v___x_2075_);
                    lean_ctor_set(v_reuseFailAlloc_2078_, 4, v_r_1957_);
                    v___x_2077_ = v_reuseFailAlloc_2078_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_2077_;
            }
            47 => {
                v___x_2084_ = lean_unsigned_to_nat(2);
                if v_isShared_1962_ == 0 {
                    lean_ctor_set(v___x_1961_, 4, v___x_2083_);
                    lean_ctor_set(v___x_1961_, 3, v_r_1957_);
                    lean_ctor_set(v___x_1961_, 2, v_v_2081_);
                    lean_ctor_set(v___x_1961_, 1, v_k_2080_);
                    lean_ctor_set(v___x_1961_, 0, v___x_2084_);
                    v___x_2086_ = v___x_1961_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
                    lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_k_2080_);
                    lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_v_2081_);
                    lean_ctor_set(v_reuseFailAlloc_2087_, 3, v_r_1957_);
                    lean_ctor_set(v_reuseFailAlloc_2087_, 4, v___x_2083_);
                    v___x_2086_ = v_reuseFailAlloc_2087_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_2086_;
            }
            49 => {
                v___x_2104_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(
                    v_k_1954_, v_v_1955_, v_l_1956_, v_r_1957_,
                );
                v_tree_2105_ = lean_ctor_get(v___x_2104_, 2);
                lean_inc(v_tree_2105_);
                if lean_obj_tag(v_tree_2105_) == 0 {
                    v_k_2106_ = lean_ctor_get(v___x_2104_, 0);
                    lean_inc(v_k_2106_);
                    v_v_2107_ = lean_ctor_get(v___x_2104_, 1);
                    lean_inc(v_v_2107_);
                    lean_dec_ref(v___x_2104_);
                    v_size_2108_ = lean_ctor_get(v_tree_2105_, 0);
                    v___x_2109_ = lean_unsigned_to_nat(3);
                    v___x_2110_ = lean_nat_mul(v___x_2109_, v_size_2108_);
                    v___x_2111_ = lean_nat_dec_lt(v___x_2110_, v_size_1948_);
                    lean_dec(v___x_2110_);
                    if v___x_2111_ == 0 {
                        lean_dec(v_r_1952_);
                        v___x_2112_ = lean_nat_add(v___x_1958_, v_size_1948_);
                        v___x_2113_ = lean_nat_add(v___x_2112_, v_size_2108_);
                        lean_dec(v___x_2112_);
                        if v_isShared_2103_ == 0 {
                            lean_ctor_set(v___x_2102_, 4, v_tree_2105_);
                            lean_ctor_set(v___x_2102_, 3, v_l_1775_);
                            lean_ctor_set(v___x_2102_, 2, v_v_2107_);
                            lean_ctor_set(v___x_2102_, 1, v_k_2106_);
                            lean_ctor_set(v___x_2102_, 0, v___x_2113_);
                            v___x_2115_ = v___x_2102_;
                            state = 50;
                            continue;
                        } else {
                            v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
                            lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_k_2106_);
                            lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_v_2107_);
                            lean_ctor_set(v_reuseFailAlloc_2116_, 3, v_l_1775_);
                            lean_ctor_set(v_reuseFailAlloc_2116_, 4, v_tree_2105_);
                            v___x_2115_ = v_reuseFailAlloc_2116_;
                            state = 50;
                            continue;
                        }
                    } else {
                        lean_inc(v_l_1951_);
                        lean_inc(v_v_1950_);
                        lean_inc(v_k_1949_);
                        lean_inc(v_size_1948_);
                        v_isSharedCheck_2182_ = (!lean_is_exclusive(v_l_1775_)) as u8;
                        if v_isSharedCheck_2182_ == 0 {
                            v_unused_2183_ = lean_ctor_get(v_l_1775_, 4);
                            lean_dec(v_unused_2183_);
                            v_unused_2184_ = lean_ctor_get(v_l_1775_, 3);
                            lean_dec(v_unused_2184_);
                            v_unused_2185_ = lean_ctor_get(v_l_1775_, 2);
                            lean_dec(v_unused_2185_);
                            v_unused_2186_ = lean_ctor_get(v_l_1775_, 1);
                            lean_dec(v_unused_2186_);
                            v_unused_2187_ = lean_ctor_get(v_l_1775_, 0);
                            lean_dec(v_unused_2187_);
                            v___x_2118_ = v_l_1775_;
                            v_isShared_2119_ = v_isSharedCheck_2182_;
                            state = 51;
                            continue;
                        } else {
                            lean_dec(v_l_1775_);
                            v___x_2118_ = lean_box(0);
                            v_isShared_2119_ = v_isSharedCheck_2182_;
                            state = 51;
                            continue;
                        }
                    }
                } else {
                    if lean_obj_tag(v_l_1951_) == 0 {
                        lean_inc_ref(v_l_1951_);
                        lean_inc(v_v_1950_);
                        lean_inc(v_k_1949_);
                        lean_inc(v_size_1948_);
                        v_isSharedCheck_2211_ = (!lean_is_exclusive(v_l_1775_)) as u8;
                        if v_isSharedCheck_2211_ == 0 {
                            v_unused_2212_ = lean_ctor_get(v_l_1775_, 4);
                            lean_dec(v_unused_2212_);
                            v_unused_2213_ = lean_ctor_get(v_l_1775_, 3);
                            lean_dec(v_unused_2213_);
                            v_unused_2214_ = lean_ctor_get(v_l_1775_, 2);
                            lean_dec(v_unused_2214_);
                            v_unused_2215_ = lean_ctor_get(v_l_1775_, 1);
                            lean_dec(v_unused_2215_);
                            v_unused_2216_ = lean_ctor_get(v_l_1775_, 0);
                            lean_dec(v_unused_2216_);
                            v___x_2189_ = v_l_1775_;
                            v_isShared_2190_ = v_isSharedCheck_2211_;
                            state = 61;
                            continue;
                        } else {
                            lean_dec(v_l_1775_);
                            v___x_2189_ = lean_box(0);
                            v_isShared_2190_ = v_isSharedCheck_2211_;
                            state = 61;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v_r_1952_) == 0 {
                            lean_inc(v_l_1951_);
                            lean_inc(v_v_1950_);
                            lean_inc(v_k_1949_);
                            v_isSharedCheck_2241_ = (!lean_is_exclusive(v_l_1775_)) as u8;
                            if v_isSharedCheck_2241_ == 0 {
                                v_unused_2242_ = lean_ctor_get(v_l_1775_, 4);
                                lean_dec(v_unused_2242_);
                                v_unused_2243_ = lean_ctor_get(v_l_1775_, 3);
                                lean_dec(v_unused_2243_);
                                v_unused_2244_ = lean_ctor_get(v_l_1775_, 2);
                                lean_dec(v_unused_2244_);
                                v_unused_2245_ = lean_ctor_get(v_l_1775_, 1);
                                lean_dec(v_unused_2245_);
                                v_unused_2246_ = lean_ctor_get(v_l_1775_, 0);
                                lean_dec(v_unused_2246_);
                                v___x_2218_ = v_l_1775_;
                                v_isShared_2219_ = v_isSharedCheck_2241_;
                                state = 66;
                                continue;
                            } else {
                                lean_dec(v_l_1775_);
                                v___x_2218_ = lean_box(0);
                                v_isShared_2219_ = v_isSharedCheck_2241_;
                                state = 66;
                                continue;
                            }
                        } else {
                            v_k_2247_ = lean_ctor_get(v___x_2104_, 0);
                            lean_inc(v_k_2247_);
                            v_v_2248_ = lean_ctor_get(v___x_2104_, 1);
                            lean_inc(v_v_2248_);
                            lean_dec_ref(v___x_2104_);
                            v___x_2249_ = lean_unsigned_to_nat(2);
                            if v_isShared_2103_ == 0 {
                                lean_ctor_set(v___x_2102_, 4, v_r_1952_);
                                lean_ctor_set(v___x_2102_, 3, v_l_1775_);
                                lean_ctor_set(v___x_2102_, 2, v_v_2248_);
                                lean_ctor_set(v___x_2102_, 1, v_k_2247_);
                                lean_ctor_set(v___x_2102_, 0, v___x_2249_);
                                v___x_2251_ = v___x_2102_;
                                state = 71;
                                continue;
                            } else {
                                v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
                                lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_k_2247_);
                                lean_ctor_set(v_reuseFailAlloc_2252_, 2, v_v_2248_);
                                lean_ctor_set(v_reuseFailAlloc_2252_, 3, v_l_1775_);
                                lean_ctor_set(v_reuseFailAlloc_2252_, 4, v_r_1952_);
                                v___x_2251_ = v_reuseFailAlloc_2252_;
                                state = 71;
                                continue;
                            }
                        }
                    }
                }
            }
            50 => {
                return v___x_2115_;
            }
            51 => {
                v_size_2120_ = lean_ctor_get(v_l_1951_, 0);
                v_size_2121_ = lean_ctor_get(v_r_1952_, 0);
                v_k_2122_ = lean_ctor_get(v_r_1952_, 1);
                v_v_2123_ = lean_ctor_get(v_r_1952_, 2);
                v_l_2124_ = lean_ctor_get(v_r_1952_, 3);
                v_r_2125_ = lean_ctor_get(v_r_1952_, 4);
                v___x_2126_ = lean_unsigned_to_nat(2);
                v___x_2127_ = lean_nat_mul(v___x_2126_, v_size_2120_);
                v___x_2128_ = lean_nat_dec_lt(v_size_2121_, v___x_2127_);
                lean_dec(v___x_2127_);
                if v___x_2128_ == 0 {
                    lean_inc(v_r_2125_);
                    lean_inc(v_l_2124_);
                    lean_inc(v_v_2123_);
                    lean_inc(v_k_2122_);
                    lean_del_object(v___x_2118_);
                    v_isSharedCheck_2166_ = (!lean_is_exclusive(v_r_1952_)) as u8;
                    if v_isSharedCheck_2166_ == 0 {
                        v_unused_2167_ = lean_ctor_get(v_r_1952_, 4);
                        lean_dec(v_unused_2167_);
                        v_unused_2168_ = lean_ctor_get(v_r_1952_, 3);
                        lean_dec(v_unused_2168_);
                        v_unused_2169_ = lean_ctor_get(v_r_1952_, 2);
                        lean_dec(v_unused_2169_);
                        v_unused_2170_ = lean_ctor_get(v_r_1952_, 1);
                        lean_dec(v_unused_2170_);
                        v_unused_2171_ = lean_ctor_get(v_r_1952_, 0);
                        lean_dec(v_unused_2171_);
                        v___x_2130_ = v_r_1952_;
                        v_isShared_2131_ = v_isSharedCheck_2166_;
                        state = 52;
                        continue;
                    } else {
                        lean_dec(v_r_1952_);
                        v___x_2130_ = lean_box(0);
                        v_isShared_2131_ = v_isSharedCheck_2166_;
                        state = 52;
                        continue;
                    }
                } else {
                    v___x_2172_ = lean_nat_add(v___x_1958_, v_size_1948_);
                    lean_dec(v_size_1948_);
                    v___x_2173_ = lean_nat_add(v___x_2172_, v_size_2108_);
                    lean_dec(v___x_2172_);
                    v___x_2174_ = lean_nat_add(v___x_1958_, v_size_2108_);
                    v___x_2175_ = lean_nat_add(v___x_2174_, v_size_2121_);
                    lean_dec(v___x_2174_);
                    if v_isShared_2103_ == 0 {
                        lean_ctor_set(v___x_2102_, 4, v_tree_2105_);
                        lean_ctor_set(v___x_2102_, 3, v_r_1952_);
                        lean_ctor_set(v___x_2102_, 2, v_v_2107_);
                        lean_ctor_set(v___x_2102_, 1, v_k_2106_);
                        lean_ctor_set(v___x_2102_, 0, v___x_2175_);
                        v___x_2177_ = v___x_2102_;
                        state = 59;
                        continue;
                    } else {
                        v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2175_);
                        lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_k_2106_);
                        lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_v_2107_);
                        lean_ctor_set(v_reuseFailAlloc_2181_, 3, v_r_1952_);
                        lean_ctor_set(v_reuseFailAlloc_2181_, 4, v_tree_2105_);
                        v___x_2177_ = v_reuseFailAlloc_2181_;
                        state = 59;
                        continue;
                    }
                }
            }
            52 => {
                v___x_2132_ = lean_nat_add(v___x_1958_, v_size_1948_);
                lean_dec(v_size_1948_);
                v___x_2133_ = lean_nat_add(v___x_2132_, v_size_2108_);
                lean_dec(v___x_2132_);
                v___x_2154_ = lean_nat_add(v___x_1958_, v_size_2120_);
                if lean_obj_tag(v_l_2124_) == 0 {
                    v_size_2164_ = lean_ctor_get(v_l_2124_, 0);
                    lean_inc(v_size_2164_);
                    v___y_2156_ = v_size_2164_;
                    state = 57;
                    continue;
                } else {
                    v___x_2165_ = lean_unsigned_to_nat(0);
                    v___y_2156_ = v___x_2165_;
                    state = 57;
                    continue;
                }
            }
            53 => {
                v___x_2138_ = lean_nat_add(v___y_2136_, v___y_2137_);
                lean_dec(v___y_2137_);
                lean_dec(v___y_2136_);
                lean_inc_ref(v_tree_2105_);
                if v_isShared_2131_ == 0 {
                    lean_ctor_set(v___x_2130_, 4, v_tree_2105_);
                    lean_ctor_set(v___x_2130_, 3, v_r_2125_);
                    lean_ctor_set(v___x_2130_, 2, v_v_2107_);
                    lean_ctor_set(v___x_2130_, 1, v_k_2106_);
                    lean_ctor_set(v___x_2130_, 0, v___x_2138_);
                    v___x_2140_ = v___x_2130_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2138_);
                    lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_k_2106_);
                    lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_v_2107_);
                    lean_ctor_set(v_reuseFailAlloc_2153_, 3, v_r_2125_);
                    lean_ctor_set(v_reuseFailAlloc_2153_, 4, v_tree_2105_);
                    v___x_2140_ = v_reuseFailAlloc_2153_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                v_isSharedCheck_2147_ = (!lean_is_exclusive(v_tree_2105_)) as u8;
                if v_isSharedCheck_2147_ == 0 {
                    v_unused_2148_ = lean_ctor_get(v_tree_2105_, 4);
                    lean_dec(v_unused_2148_);
                    v_unused_2149_ = lean_ctor_get(v_tree_2105_, 3);
                    lean_dec(v_unused_2149_);
                    v_unused_2150_ = lean_ctor_get(v_tree_2105_, 2);
                    lean_dec(v_unused_2150_);
                    v_unused_2151_ = lean_ctor_get(v_tree_2105_, 1);
                    lean_dec(v_unused_2151_);
                    v_unused_2152_ = lean_ctor_get(v_tree_2105_, 0);
                    lean_dec(v_unused_2152_);
                    v___x_2142_ = v_tree_2105_;
                    v_isShared_2143_ = v_isSharedCheck_2147_;
                    state = 55;
                    continue;
                } else {
                    lean_dec(v_tree_2105_);
                    v___x_2142_ = lean_box(0);
                    v_isShared_2143_ = v_isSharedCheck_2147_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                if v_isShared_2143_ == 0 {
                    lean_ctor_set(v___x_2142_, 4, v___x_2140_);
                    lean_ctor_set(v___x_2142_, 3, v___y_2135_);
                    lean_ctor_set(v___x_2142_, 2, v_v_2123_);
                    lean_ctor_set(v___x_2142_, 1, v_k_2122_);
                    lean_ctor_set(v___x_2142_, 0, v___x_2133_);
                    v___x_2145_ = v___x_2142_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2133_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_k_2122_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 2, v_v_2123_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 3, v___y_2135_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 4, v___x_2140_);
                    v___x_2145_ = v_reuseFailAlloc_2146_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_2145_;
            }
            57 => {
                v___x_2157_ = lean_nat_add(v___x_2154_, v___y_2156_);
                lean_dec(v___y_2156_);
                lean_dec(v___x_2154_);
                if v_isShared_2103_ == 0 {
                    lean_ctor_set(v___x_2102_, 4, v_l_2124_);
                    lean_ctor_set(v___x_2102_, 3, v_l_1951_);
                    lean_ctor_set(v___x_2102_, 2, v_v_1950_);
                    lean_ctor_set(v___x_2102_, 1, v_k_1949_);
                    lean_ctor_set(v___x_2102_, 0, v___x_2157_);
                    v___x_2159_ = v___x_2102_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2157_);
                    lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_k_1949_);
                    lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_v_1950_);
                    lean_ctor_set(v_reuseFailAlloc_2163_, 3, v_l_1951_);
                    lean_ctor_set(v_reuseFailAlloc_2163_, 4, v_l_2124_);
                    v___x_2159_ = v_reuseFailAlloc_2163_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                v___x_2160_ = lean_nat_add(v___x_1958_, v_size_2108_);
                if lean_obj_tag(v_r_2125_) == 0 {
                    v_size_2161_ = lean_ctor_get(v_r_2125_, 0);
                    lean_inc(v_size_2161_);
                    v___y_2135_ = v___x_2159_;
                    v___y_2136_ = v___x_2160_;
                    v___y_2137_ = v_size_2161_;
                    state = 53;
                    continue;
                } else {
                    v___x_2162_ = lean_unsigned_to_nat(0);
                    v___y_2135_ = v___x_2159_;
                    v___y_2136_ = v___x_2160_;
                    v___y_2137_ = v___x_2162_;
                    state = 53;
                    continue;
                }
            }
            59 => {
                if v_isShared_2119_ == 0 {
                    lean_ctor_set(v___x_2118_, 4, v___x_2177_);
                    lean_ctor_set(v___x_2118_, 0, v___x_2173_);
                    v___x_2179_ = v___x_2118_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2173_);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_k_1949_);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_v_1950_);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 3, v_l_1951_);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 4, v___x_2177_);
                    v___x_2179_ = v_reuseFailAlloc_2180_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_2179_;
            }
            61 => {
                if lean_obj_tag(v_r_1952_) == 0 {
                    v_k_2191_ = lean_ctor_get(v___x_2104_, 0);
                    lean_inc(v_k_2191_);
                    v_v_2192_ = lean_ctor_get(v___x_2104_, 1);
                    lean_inc(v_v_2192_);
                    lean_dec_ref(v___x_2104_);
                    v_size_2193_ = lean_ctor_get(v_r_1952_, 0);
                    v___x_2194_ = lean_nat_add(v___x_1958_, v_size_1948_);
                    lean_dec(v_size_1948_);
                    v___x_2195_ = lean_nat_add(v___x_1958_, v_size_2193_);
                    if v_isShared_2103_ == 0 {
                        lean_ctor_set(v___x_2102_, 4, v_tree_2105_);
                        lean_ctor_set(v___x_2102_, 3, v_r_1952_);
                        lean_ctor_set(v___x_2102_, 2, v_v_2192_);
                        lean_ctor_set(v___x_2102_, 1, v_k_2191_);
                        lean_ctor_set(v___x_2102_, 0, v___x_2195_);
                        v___x_2197_ = v___x_2102_;
                        state = 62;
                        continue;
                    } else {
                        v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2195_);
                        lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_k_2191_);
                        lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_v_2192_);
                        lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_r_1952_);
                        lean_ctor_set(v_reuseFailAlloc_2201_, 4, v_tree_2105_);
                        v___x_2197_ = v_reuseFailAlloc_2201_;
                        state = 62;
                        continue;
                    }
                } else {
                    lean_dec(v_size_1948_);
                    v_k_2202_ = lean_ctor_get(v___x_2104_, 0);
                    lean_inc(v_k_2202_);
                    v_v_2203_ = lean_ctor_get(v___x_2104_, 1);
                    lean_inc(v_v_2203_);
                    lean_dec_ref(v___x_2104_);
                    v___x_2204_ = lean_unsigned_to_nat(3);
                    if v_isShared_2103_ == 0 {
                        lean_ctor_set(v___x_2102_, 4, v_r_1952_);
                        lean_ctor_set(v___x_2102_, 3, v_r_1952_);
                        lean_ctor_set(v___x_2102_, 2, v_v_2203_);
                        lean_ctor_set(v___x_2102_, 1, v_k_2202_);
                        lean_ctor_set(v___x_2102_, 0, v___x_1958_);
                        v___x_2206_ = v___x_2102_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_1958_);
                        lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_k_2202_);
                        lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_v_2203_);
                        lean_ctor_set(v_reuseFailAlloc_2210_, 3, v_r_1952_);
                        lean_ctor_set(v_reuseFailAlloc_2210_, 4, v_r_1952_);
                        v___x_2206_ = v_reuseFailAlloc_2210_;
                        state = 64;
                        continue;
                    }
                }
            }
            62 => {
                if v_isShared_2190_ == 0 {
                    lean_ctor_set(v___x_2189_, 4, v___x_2197_);
                    lean_ctor_set(v___x_2189_, 0, v___x_2194_);
                    v___x_2199_ = v___x_2189_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2194_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_k_1949_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_v_1950_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 3, v_l_1951_);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 4, v___x_2197_);
                    v___x_2199_ = v_reuseFailAlloc_2200_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_2199_;
            }
            64 => {
                if v_isShared_2190_ == 0 {
                    lean_ctor_set(v___x_2189_, 4, v___x_2206_);
                    lean_ctor_set(v___x_2189_, 0, v___x_2204_);
                    v___x_2208_ = v___x_2189_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2204_);
                    lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_k_1949_);
                    lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_v_1950_);
                    lean_ctor_set(v_reuseFailAlloc_2209_, 3, v_l_1951_);
                    lean_ctor_set(v_reuseFailAlloc_2209_, 4, v___x_2206_);
                    v___x_2208_ = v_reuseFailAlloc_2209_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_2208_;
            }
            66 => {
                v_k_2220_ = lean_ctor_get(v___x_2104_, 0);
                lean_inc(v_k_2220_);
                v_v_2221_ = lean_ctor_get(v___x_2104_, 1);
                lean_inc(v_v_2221_);
                lean_dec_ref(v___x_2104_);
                v_k_2222_ = lean_ctor_get(v_r_1952_, 1);
                v_v_2223_ = lean_ctor_get(v_r_1952_, 2);
                v_isSharedCheck_2237_ = (!lean_is_exclusive(v_r_1952_)) as u8;
                if v_isSharedCheck_2237_ == 0 {
                    v_unused_2238_ = lean_ctor_get(v_r_1952_, 4);
                    lean_dec(v_unused_2238_);
                    v_unused_2239_ = lean_ctor_get(v_r_1952_, 3);
                    lean_dec(v_unused_2239_);
                    v_unused_2240_ = lean_ctor_get(v_r_1952_, 0);
                    lean_dec(v_unused_2240_);
                    v___x_2225_ = v_r_1952_;
                    v_isShared_2226_ = v_isSharedCheck_2237_;
                    state = 67;
                    continue;
                } else {
                    lean_inc(v_v_2223_);
                    lean_inc(v_k_2222_);
                    lean_dec(v_r_1952_);
                    v___x_2225_ = lean_box(0);
                    v_isShared_2226_ = v_isSharedCheck_2237_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                v___x_2227_ = lean_unsigned_to_nat(3);
                if v_isShared_2226_ == 0 {
                    lean_ctor_set(v___x_2225_, 4, v_l_1951_);
                    lean_ctor_set(v___x_2225_, 3, v_l_1951_);
                    lean_ctor_set(v___x_2225_, 2, v_v_1950_);
                    lean_ctor_set(v___x_2225_, 1, v_k_1949_);
                    lean_ctor_set(v___x_2225_, 0, v___x_1958_);
                    v___x_2229_ = v___x_2225_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_1958_);
                    lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_k_1949_);
                    lean_ctor_set(v_reuseFailAlloc_2236_, 2, v_v_1950_);
                    lean_ctor_set(v_reuseFailAlloc_2236_, 3, v_l_1951_);
                    lean_ctor_set(v_reuseFailAlloc_2236_, 4, v_l_1951_);
                    v___x_2229_ = v_reuseFailAlloc_2236_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                if v_isShared_2103_ == 0 {
                    lean_ctor_set(v___x_2102_, 4, v_l_1951_);
                    lean_ctor_set(v___x_2102_, 3, v_l_1951_);
                    lean_ctor_set(v___x_2102_, 2, v_v_2221_);
                    lean_ctor_set(v___x_2102_, 1, v_k_2220_);
                    lean_ctor_set(v___x_2102_, 0, v___x_1958_);
                    v___x_2231_ = v___x_2102_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_1958_);
                    lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_k_2220_);
                    lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_v_2221_);
                    lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_l_1951_);
                    lean_ctor_set(v_reuseFailAlloc_2235_, 4, v_l_1951_);
                    v___x_2231_ = v_reuseFailAlloc_2235_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                if v_isShared_2219_ == 0 {
                    lean_ctor_set(v___x_2218_, 4, v___x_2231_);
                    lean_ctor_set(v___x_2218_, 3, v___x_2229_);
                    lean_ctor_set(v___x_2218_, 2, v_v_2223_);
                    lean_ctor_set(v___x_2218_, 1, v_k_2222_);
                    lean_ctor_set(v___x_2218_, 0, v___x_2227_);
                    v___x_2233_ = v___x_2218_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2227_);
                    lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_k_2222_);
                    lean_ctor_set(v_reuseFailAlloc_2234_, 2, v_v_2223_);
                    lean_ctor_set(v_reuseFailAlloc_2234_, 3, v___x_2229_);
                    lean_ctor_set(v_reuseFailAlloc_2234_, 4, v___x_2231_);
                    v___x_2233_ = v_reuseFailAlloc_2234_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_2233_;
            }
            71 => {
                return v___x_2251_;
            }
            72 => {
                return v___x_2273_;
            }
            73 => {
                v_size_2278_ = lean_ctor_get(v_l_2265_, 0);
                v_k_2279_ = lean_ctor_get(v_l_2265_, 1);
                v_v_2280_ = lean_ctor_get(v_l_2265_, 2);
                v_l_2281_ = lean_ctor_get(v_l_2265_, 3);
                v_r_2282_ = lean_ctor_get(v_l_2265_, 4);
                v_size_2283_ = lean_ctor_get(v_r_2266_, 0);
                v___x_2284_ = lean_unsigned_to_nat(2);
                v___x_2285_ = lean_nat_mul(v___x_2284_, v_size_2283_);
                v___x_2286_ = lean_nat_dec_lt(v_size_2278_, v___x_2285_);
                lean_dec(v___x_2285_);
                if v___x_2286_ == 0 {
                    lean_inc(v_r_2282_);
                    lean_inc(v_l_2281_);
                    lean_inc(v_v_2280_);
                    lean_inc(v_k_2279_);
                    v_isSharedCheck_2314_ = (!lean_is_exclusive(v_l_2265_)) as u8;
                    if v_isSharedCheck_2314_ == 0 {
                        v_unused_2315_ = lean_ctor_get(v_l_2265_, 4);
                        lean_dec(v_unused_2315_);
                        v_unused_2316_ = lean_ctor_get(v_l_2265_, 3);
                        lean_dec(v_unused_2316_);
                        v_unused_2317_ = lean_ctor_get(v_l_2265_, 2);
                        lean_dec(v_unused_2317_);
                        v_unused_2318_ = lean_ctor_get(v_l_2265_, 1);
                        lean_dec(v_unused_2318_);
                        v_unused_2319_ = lean_ctor_get(v_l_2265_, 0);
                        lean_dec(v_unused_2319_);
                        v___x_2288_ = v_l_2265_;
                        v_isShared_2289_ = v_isSharedCheck_2314_;
                        state = 74;
                        continue;
                    } else {
                        lean_dec(v_l_2265_);
                        v___x_2288_ = lean_box(0);
                        v_isShared_2289_ = v_isSharedCheck_2314_;
                        state = 74;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1778_);
                    v___x_2320_ = lean_nat_add(v___x_2260_, v_size_2261_);
                    lean_dec(v_size_2261_);
                    v___x_2321_ = lean_nat_add(v___x_2320_, v_size_2262_);
                    lean_dec(v_size_2262_);
                    v___x_2322_ = lean_nat_add(v___x_2320_, v_size_2278_);
                    lean_dec(v___x_2320_);
                    lean_inc_ref(v_impl_2259_);
                    if v_isShared_2277_ == 0 {
                        lean_ctor_set(v___x_2276_, 4, v_l_2265_);
                        lean_ctor_set(v___x_2276_, 3, v_impl_2259_);
                        lean_ctor_set(v___x_2276_, 2, v_v_1774_);
                        lean_ctor_set(v___x_2276_, 1, v_k_1773_);
                        lean_ctor_set(v___x_2276_, 0, v___x_2322_);
                        v___x_2324_ = v___x_2276_;
                        state = 80;
                        continue;
                    } else {
                        v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2322_);
                        lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_k_1773_);
                        lean_ctor_set(v_reuseFailAlloc_2337_, 2, v_v_1774_);
                        lean_ctor_set(v_reuseFailAlloc_2337_, 3, v_impl_2259_);
                        lean_ctor_set(v_reuseFailAlloc_2337_, 4, v_l_2265_);
                        v___x_2324_ = v_reuseFailAlloc_2337_;
                        state = 80;
                        continue;
                    }
                }
            }
            74 => {
                v___x_2290_ = lean_nat_add(v___x_2260_, v_size_2261_);
                lean_dec(v_size_2261_);
                v___x_2291_ = lean_nat_add(v___x_2290_, v_size_2262_);
                lean_dec(v_size_2262_);
                if lean_obj_tag(v_l_2281_) == 0 {
                    v_size_2312_ = lean_ctor_get(v_l_2281_, 0);
                    lean_inc(v_size_2312_);
                    v___y_2304_ = v_size_2312_;
                    state = 78;
                    continue;
                } else {
                    v___x_2313_ = lean_unsigned_to_nat(0);
                    v___y_2304_ = v___x_2313_;
                    state = 78;
                    continue;
                }
            }
            75 => {
                v___x_2296_ = lean_nat_add(v___y_2293_, v___y_2295_);
                lean_dec(v___y_2295_);
                lean_dec(v___y_2293_);
                if v_isShared_2289_ == 0 {
                    lean_ctor_set(v___x_2288_, 4, v_r_2266_);
                    lean_ctor_set(v___x_2288_, 3, v_r_2282_);
                    lean_ctor_set(v___x_2288_, 2, v_v_2264_);
                    lean_ctor_set(v___x_2288_, 1, v_k_2263_);
                    lean_ctor_set(v___x_2288_, 0, v___x_2296_);
                    v___x_2298_ = v___x_2288_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2296_);
                    lean_ctor_set(v_reuseFailAlloc_2302_, 1, v_k_2263_);
                    lean_ctor_set(v_reuseFailAlloc_2302_, 2, v_v_2264_);
                    lean_ctor_set(v_reuseFailAlloc_2302_, 3, v_r_2282_);
                    lean_ctor_set(v_reuseFailAlloc_2302_, 4, v_r_2266_);
                    v___x_2298_ = v_reuseFailAlloc_2302_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                if v_isShared_2277_ == 0 {
                    lean_ctor_set(v___x_2276_, 4, v___x_2298_);
                    lean_ctor_set(v___x_2276_, 3, v___y_2294_);
                    lean_ctor_set(v___x_2276_, 2, v_v_2280_);
                    lean_ctor_set(v___x_2276_, 1, v_k_2279_);
                    lean_ctor_set(v___x_2276_, 0, v___x_2291_);
                    v___x_2300_ = v___x_2276_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2291_);
                    lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_k_2279_);
                    lean_ctor_set(v_reuseFailAlloc_2301_, 2, v_v_2280_);
                    lean_ctor_set(v_reuseFailAlloc_2301_, 3, v___y_2294_);
                    lean_ctor_set(v_reuseFailAlloc_2301_, 4, v___x_2298_);
                    v___x_2300_ = v_reuseFailAlloc_2301_;
                    state = 77;
                    continue;
                }
            }
            77 => {
                return v___x_2300_;
            }
            78 => {
                v___x_2305_ = lean_nat_add(v___x_2290_, v___y_2304_);
                lean_dec(v___y_2304_);
                lean_dec(v___x_2290_);
                if v_isShared_1779_ == 0 {
                    lean_ctor_set(v___x_1778_, 4, v_l_2281_);
                    lean_ctor_set(v___x_1778_, 3, v_impl_2259_);
                    lean_ctor_set(v___x_1778_, 0, v___x_2305_);
                    v___x_2307_ = v___x_1778_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2305_);
                    lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_k_1773_);
                    lean_ctor_set(v_reuseFailAlloc_2311_, 2, v_v_1774_);
                    lean_ctor_set(v_reuseFailAlloc_2311_, 3, v_impl_2259_);
                    lean_ctor_set(v_reuseFailAlloc_2311_, 4, v_l_2281_);
                    v___x_2307_ = v_reuseFailAlloc_2311_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                v___x_2308_ = lean_nat_add(v___x_2260_, v_size_2283_);
                if lean_obj_tag(v_r_2282_) == 0 {
                    v_size_2309_ = lean_ctor_get(v_r_2282_, 0);
                    lean_inc(v_size_2309_);
                    v___y_2293_ = v___x_2308_;
                    v___y_2294_ = v___x_2307_;
                    v___y_2295_ = v_size_2309_;
                    state = 75;
                    continue;
                } else {
                    v___x_2310_ = lean_unsigned_to_nat(0);
                    v___y_2293_ = v___x_2308_;
                    v___y_2294_ = v___x_2307_;
                    v___y_2295_ = v___x_2310_;
                    state = 75;
                    continue;
                }
            }
            80 => {
                v_isSharedCheck_2331_ = (!lean_is_exclusive(v_impl_2259_)) as u8;
                if v_isSharedCheck_2331_ == 0 {
                    v_unused_2332_ = lean_ctor_get(v_impl_2259_, 4);
                    lean_dec(v_unused_2332_);
                    v_unused_2333_ = lean_ctor_get(v_impl_2259_, 3);
                    lean_dec(v_unused_2333_);
                    v_unused_2334_ = lean_ctor_get(v_impl_2259_, 2);
                    lean_dec(v_unused_2334_);
                    v_unused_2335_ = lean_ctor_get(v_impl_2259_, 1);
                    lean_dec(v_unused_2335_);
                    v_unused_2336_ = lean_ctor_get(v_impl_2259_, 0);
                    lean_dec(v_unused_2336_);
                    v___x_2326_ = v_impl_2259_;
                    v_isShared_2327_ = v_isSharedCheck_2331_;
                    state = 81;
                    continue;
                } else {
                    lean_dec(v_impl_2259_);
                    v___x_2326_ = lean_box(0);
                    v_isShared_2327_ = v_isSharedCheck_2331_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                if v_isShared_2327_ == 0 {
                    lean_ctor_set(v___x_2326_, 4, v_r_2266_);
                    lean_ctor_set(v___x_2326_, 3, v___x_2324_);
                    lean_ctor_set(v___x_2326_, 2, v_v_2264_);
                    lean_ctor_set(v___x_2326_, 1, v_k_2263_);
                    lean_ctor_set(v___x_2326_, 0, v___x_2321_);
                    v___x_2329_ = v___x_2326_;
                    state = 82;
                    continue;
                } else {
                    v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2321_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_k_2263_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 2, v_v_2264_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 3, v___x_2324_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 4, v_r_2266_);
                    v___x_2329_ = v_reuseFailAlloc_2330_;
                    state = 82;
                    continue;
                }
            }
            82 => {
                return v___x_2329_;
            }
            83 => {
                return v___x_2347_;
            }
            84 => {
                v_size_2357_ = lean_ctor_get(v_l_2349_, 0);
                v___x_2358_ = lean_nat_add(v___x_2260_, v_size_2351_);
                lean_dec(v_size_2351_);
                v___x_2359_ = lean_nat_add(v___x_2260_, v_size_2357_);
                if v_isShared_2356_ == 0 {
                    lean_ctor_set(v___x_2355_, 4, v_l_2349_);
                    lean_ctor_set(v___x_2355_, 3, v_impl_2259_);
                    lean_ctor_set(v___x_2355_, 2, v_v_1774_);
                    lean_ctor_set(v___x_2355_, 1, v_k_1773_);
                    lean_ctor_set(v___x_2355_, 0, v___x_2359_);
                    v___x_2361_ = v___x_2355_;
                    state = 85;
                    continue;
                } else {
                    v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2359_);
                    lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_k_1773_);
                    lean_ctor_set(v_reuseFailAlloc_2365_, 2, v_v_1774_);
                    lean_ctor_set(v_reuseFailAlloc_2365_, 3, v_impl_2259_);
                    lean_ctor_set(v_reuseFailAlloc_2365_, 4, v_l_2349_);
                    v___x_2361_ = v_reuseFailAlloc_2365_;
                    state = 85;
                    continue;
                }
            }
            85 => {
                if v_isShared_1779_ == 0 {
                    lean_ctor_set(v___x_1778_, 4, v_r_2350_);
                    lean_ctor_set(v___x_1778_, 3, v___x_2361_);
                    lean_ctor_set(v___x_1778_, 2, v_v_2353_);
                    lean_ctor_set(v___x_1778_, 1, v_k_2352_);
                    lean_ctor_set(v___x_1778_, 0, v___x_2358_);
                    v___x_2363_ = v___x_1778_;
                    state = 86;
                    continue;
                } else {
                    v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2358_);
                    lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_k_2352_);
                    lean_ctor_set(v_reuseFailAlloc_2364_, 2, v_v_2353_);
                    lean_ctor_set(v_reuseFailAlloc_2364_, 3, v___x_2361_);
                    lean_ctor_set(v_reuseFailAlloc_2364_, 4, v_r_2350_);
                    v___x_2363_ = v_reuseFailAlloc_2364_;
                    state = 86;
                    continue;
                }
            }
            86 => {
                return v___x_2363_;
            }
            87 => {
                v_k_2374_ = lean_ctor_get(v_l_2349_, 1);
                v_v_2375_ = lean_ctor_get(v_l_2349_, 2);
                v_isSharedCheck_2389_ = (!lean_is_exclusive(v_l_2349_)) as u8;
                if v_isSharedCheck_2389_ == 0 {
                    v_unused_2390_ = lean_ctor_get(v_l_2349_, 4);
                    lean_dec(v_unused_2390_);
                    v_unused_2391_ = lean_ctor_get(v_l_2349_, 3);
                    lean_dec(v_unused_2391_);
                    v_unused_2392_ = lean_ctor_get(v_l_2349_, 0);
                    lean_dec(v_unused_2392_);
                    v___x_2377_ = v_l_2349_;
                    v_isShared_2378_ = v_isSharedCheck_2389_;
                    state = 88;
                    continue;
                } else {
                    lean_inc(v_v_2375_);
                    lean_inc(v_k_2374_);
                    lean_dec(v_l_2349_);
                    v___x_2377_ = lean_box(0);
                    v_isShared_2378_ = v_isSharedCheck_2389_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                v___x_2379_ = lean_unsigned_to_nat(3);
                if v_isShared_2378_ == 0 {
                    lean_ctor_set(v___x_2377_, 4, v_r_2350_);
                    lean_ctor_set(v___x_2377_, 3, v_r_2350_);
                    lean_ctor_set(v___x_2377_, 2, v_v_1774_);
                    lean_ctor_set(v___x_2377_, 1, v_k_1773_);
                    lean_ctor_set(v___x_2377_, 0, v___x_2260_);
                    v___x_2381_ = v___x_2377_;
                    state = 89;
                    continue;
                } else {
                    v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2260_);
                    lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_k_1773_);
                    lean_ctor_set(v_reuseFailAlloc_2388_, 2, v_v_1774_);
                    lean_ctor_set(v_reuseFailAlloc_2388_, 3, v_r_2350_);
                    lean_ctor_set(v_reuseFailAlloc_2388_, 4, v_r_2350_);
                    v___x_2381_ = v_reuseFailAlloc_2388_;
                    state = 89;
                    continue;
                }
            }
            89 => {
                if v_isShared_2373_ == 0 {
                    lean_ctor_set(v___x_2372_, 3, v_r_2350_);
                    lean_ctor_set(v___x_2372_, 0, v___x_2260_);
                    v___x_2383_ = v___x_2372_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2260_);
                    lean_ctor_set(v_reuseFailAlloc_2387_, 1, v_k_2369_);
                    lean_ctor_set(v_reuseFailAlloc_2387_, 2, v_v_2370_);
                    lean_ctor_set(v_reuseFailAlloc_2387_, 3, v_r_2350_);
                    lean_ctor_set(v_reuseFailAlloc_2387_, 4, v_r_2350_);
                    v___x_2383_ = v_reuseFailAlloc_2387_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_1779_ == 0 {
                    lean_ctor_set(v___x_1778_, 4, v___x_2383_);
                    lean_ctor_set(v___x_1778_, 3, v___x_2381_);
                    lean_ctor_set(v___x_1778_, 2, v_v_2375_);
                    lean_ctor_set(v___x_1778_, 1, v_k_2374_);
                    lean_ctor_set(v___x_1778_, 0, v___x_2379_);
                    v___x_2385_ = v___x_1778_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2379_);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_k_2374_);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 2, v_v_2375_);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 3, v___x_2381_);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 4, v___x_2383_);
                    v___x_2385_ = v_reuseFailAlloc_2386_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_2385_;
            }
            92 => {
                v___x_2403_ = lean_unsigned_to_nat(3);
                if v_isShared_2402_ == 0 {
                    lean_ctor_set(v___x_2401_, 4, v_l_2349_);
                    lean_ctor_set(v___x_2401_, 2, v_v_1774_);
                    lean_ctor_set(v___x_2401_, 1, v_k_1773_);
                    lean_ctor_set(v___x_2401_, 0, v___x_2260_);
                    v___x_2405_ = v___x_2401_;
                    state = 93;
                    continue;
                } else {
                    v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2260_);
                    lean_ctor_set(v_reuseFailAlloc_2409_, 1, v_k_1773_);
                    lean_ctor_set(v_reuseFailAlloc_2409_, 2, v_v_1774_);
                    lean_ctor_set(v_reuseFailAlloc_2409_, 3, v_l_2349_);
                    lean_ctor_set(v_reuseFailAlloc_2409_, 4, v_l_2349_);
                    v___x_2405_ = v_reuseFailAlloc_2409_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                if v_isShared_1779_ == 0 {
                    lean_ctor_set(v___x_1778_, 4, v_r_2397_);
                    lean_ctor_set(v___x_1778_, 3, v___x_2405_);
                    lean_ctor_set(v___x_1778_, 2, v_v_2399_);
                    lean_ctor_set(v___x_1778_, 1, v_k_2398_);
                    lean_ctor_set(v___x_1778_, 0, v___x_2403_);
                    v___x_2407_ = v___x_1778_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2403_);
                    lean_ctor_set(v_reuseFailAlloc_2408_, 1, v_k_2398_);
                    lean_ctor_set(v_reuseFailAlloc_2408_, 2, v_v_2399_);
                    lean_ctor_set(v_reuseFailAlloc_2408_, 3, v___x_2405_);
                    lean_ctor_set(v_reuseFailAlloc_2408_, 4, v_r_2397_);
                    v___x_2407_ = v_reuseFailAlloc_2408_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                return v___x_2407_;
            }
            95 => {
                if v_isShared_2419_ == 0 {
                    lean_ctor_set(v___x_2418_, 3, v_r_2397_);
                    v___x_2421_ = v___x_2418_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_size_2414_);
                    lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_k_2415_);
                    lean_ctor_set(v_reuseFailAlloc_2426_, 2, v_v_2416_);
                    lean_ctor_set(v_reuseFailAlloc_2426_, 3, v_r_2397_);
                    lean_ctor_set(v_reuseFailAlloc_2426_, 4, v_r_2397_);
                    v___x_2421_ = v_reuseFailAlloc_2426_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                v___x_2422_ = lean_unsigned_to_nat(2);
                if v_isShared_1779_ == 0 {
                    lean_ctor_set(v___x_1778_, 4, v___x_2421_);
                    lean_ctor_set(v___x_1778_, 3, v_r_2397_);
                    lean_ctor_set(v___x_1778_, 0, v___x_2422_);
                    v___x_2424_ = v___x_1778_;
                    state = 97;
                    continue;
                } else {
                    v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2422_);
                    lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_k_1773_);
                    lean_ctor_set(v_reuseFailAlloc_2425_, 2, v_v_1774_);
                    lean_ctor_set(v_reuseFailAlloc_2425_, 3, v_r_2397_);
                    lean_ctor_set(v_reuseFailAlloc_2425_, 4, v___x_2421_);
                    v___x_2424_ = v_reuseFailAlloc_2425_;
                    state = 97;
                    continue;
                }
            }
            97 => {
                return v___x_2424_;
            }
            98 => {
                return v___x_2431_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg___boxed(
    mut v_k_2435_: *mut LeanObject,
    mut v_t_2436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_boxed_2437_: u64 = 0;
    let mut v_res_2438_: *mut LeanObject = core::ptr::null_mut();
    v_k_boxed_2437_ = lean_unbox_uint64(v_k_2435_);
    lean_dec_ref(v_k_2435_);
    v_res_2438_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_boxed_2437_, v_t_2436_);
    return v_res_2438_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(
    mut v_t_2439_: *mut LeanObject,
    mut v_k_2440_: u64,
) -> *mut LeanObject {
    let mut v_k_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u64 = 0;
    let mut v___x_2446_: u8 = 0;
    let mut v___x_2447_: u64 = 0;
    let mut v___x_2448_: u8 = 0;
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2439_) == 0 {
                    v_k_2441_ = lean_ctor_get(v_t_2439_, 1);
                    v_v_2442_ = lean_ctor_get(v_t_2439_, 2);
                    v_l_2443_ = lean_ctor_get(v_t_2439_, 3);
                    v_r_2444_ = lean_ctor_get(v_t_2439_, 4);
                    v___x_2445_ = lean_unbox_uint64(v_k_2441_);
                    v___x_2446_ = lean_uint64_dec_lt(v_k_2440_, v___x_2445_);
                    if v___x_2446_ == 0 {
                        v___x_2447_ = lean_unbox_uint64(v_k_2441_);
                        v___x_2448_ = lean_uint64_dec_eq(v_k_2440_, v___x_2447_);
                        if v___x_2448_ == 0 {
                            v_t_2439_ = v_r_2444_;
                            state = 0;
                            continue;
                        } else {
                            lean_inc(v_v_2442_);
                            v___x_2450_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2450_, 0, v_v_2442_);
                            return v___x_2450_;
                        }
                    } else {
                        v_t_2439_ = v_l_2443_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_2452_ = lean_box(0);
                    return v___x_2452_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg___boxed(
    mut v_t_2453_: *mut LeanObject,
    mut v_k_2454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_boxed_2455_: u64 = 0;
    let mut v_res_2456_: *mut LeanObject = core::ptr::null_mut();
    v_k_boxed_2455_ = lean_unbox_uint64(v_k_2454_);
    lean_dec_ref(v_k_2454_);
    v_res_2456_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_t_2453_, v_k_boxed_2455_);
    lean_dec(v_t_2453_);
    return v_res_2456_;
}
pub unsafe fn l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(
    mut v_state_2457_: *mut LeanObject,
    mut v_id_2458_: u64,
    mut v_reason_2459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tokens_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2466_: usize = 0;
    let mut v___x_2467_: usize = 0;
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tokens_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_2471_: u64 = 0;
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2474_: u8 = 0;
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tokens_2461_ = lean_ctor_get(v_state_2457_, 0);
                v___x_2462_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_tokens_2461_, v_id_2458_);
                if lean_obj_tag(v___x_2462_) == 1 {
                    v_val_2463_ = lean_ctor_get(v___x_2462_, 0);
                    lean_inc(v_val_2463_);
                    lean_dec_ref_known(v___x_2462_, 1);
                    v_fst_2464_ = lean_ctor_get(v_val_2463_, 0);
                    lean_inc(v_fst_2464_);
                    v_snd_2465_ = lean_ctor_get(v_val_2463_, 1);
                    lean_inc(v_snd_2465_);
                    lean_dec(v_val_2463_);
                    v_sz_2466_ = lean_array_size(v_snd_2465_);
                    v___x_2467_ = 0usize;
                    lean_inc(v_reason_2459_);
                    v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(v_reason_2459_, v_snd_2465_, v_sz_2466_, v___x_2467_, v_state_2457_);
                    lean_dec(v_snd_2465_);
                    v___x_2469_ = l_Std_CancellationToken_cancel(v_fst_2464_, v_reason_2459_);
                    v_tokens_2470_ = lean_ctor_get(v___x_2468_, 0);
                    v_id_2471_ = lean_ctor_get_uint64(
                        v___x_2468_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_isSharedCheck_2479_ = (!lean_is_exclusive(v___x_2468_)) as u8;
                    if v_isSharedCheck_2479_ == 0 {
                        v___x_2473_ = v___x_2468_;
                        v_isShared_2474_ = v_isSharedCheck_2479_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tokens_2470_);
                        lean_dec(v___x_2468_);
                        v___x_2473_ = lean_box(0);
                        v_isShared_2474_ = v_isSharedCheck_2479_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2462_);
                    lean_dec(v_reason_2459_);
                    return v_state_2457_;
                }
            }
            1 => {
                v___x_2475_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_id_2458_, v_tokens_2470_);
                if v_isShared_2474_ == 0 {
                    lean_ctor_set(v___x_2473_, 0, v___x_2475_);
                    v___x_2477_ = v___x_2473_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2478_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_id_2471_,
                    );
                    v___x_2477_ = v_reuseFailAlloc_2478_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2477_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(
    mut v_reason_2480_: *mut LeanObject,
    mut v_as_2481_: *mut LeanObject,
    mut v_sz_2482_: usize,
    mut v_i_2483_: usize,
    mut v_b_2484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2486_: u8 = 0;
    let mut v_a_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: u64 = 0;
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: usize = 0;
    let mut v___x_2491_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2486_ = lean_usize_dec_lt(v_i_2483_, v_sz_2482_);
                if v___x_2486_ == 0 {
                    lean_dec(v_reason_2480_);
                    return v_b_2484_;
                } else {
                    v_a_2487_ = lean_array_uget_borrowed(v_as_2481_, v_i_2483_);
                    v___x_2488_ = lean_unbox_uint64(v_a_2487_);
                    lean_inc(v_reason_2480_);
                    v___x_2489_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(v_b_2484_, v___x_2488_, v_reason_2480_);
                    v___x_2490_ = 1usize;
                    v___x_2491_ = lean_usize_add(v_i_2483_, v___x_2490_);
                    v_i_2483_ = v___x_2491_;
                    v_b_2484_ = v___x_2489_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1___boxed(
    mut v_reason_2493_: *mut LeanObject,
    mut v_as_2494_: *mut LeanObject,
    mut v_sz_2495_: *mut LeanObject,
    mut v_i_2496_: *mut LeanObject,
    mut v_b_2497_: *mut LeanObject,
    mut v___y_2498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2499_: usize = 0;
    let mut v_i_boxed_2500_: usize = 0;
    let mut v_res_2501_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2499_ = lean_unbox_usize(v_sz_2495_);
    lean_dec(v_sz_2495_);
    v_i_boxed_2500_ = lean_unbox_usize(v_i_2496_);
    lean_dec(v_i_2496_);
    v_res_2501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(v_reason_2493_, v_as_2494_, v_sz_boxed_2499_, v_i_boxed_2500_, v_b_2497_);
    lean_dec_ref(v_as_2494_);
    return v_res_2501_;
}
pub unsafe fn l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren___boxed(
    mut v_state_2502_: *mut LeanObject,
    mut v_id_2503_: *mut LeanObject,
    mut v_reason_2504_: *mut LeanObject,
    mut v_a_2505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_boxed_2506_: u64 = 0;
    let mut v_res_2507_: *mut LeanObject = core::ptr::null_mut();
    v_id_boxed_2506_ = lean_unbox_uint64(v_id_2503_);
    lean_dec_ref(v_id_2503_);
    v_res_2507_ =
        l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(
            v_state_2502_,
            v_id_boxed_2506_,
            v_reason_2504_,
        );
    return v_res_2507_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(
    mut v_00_u03b4_2508_: *mut LeanObject,
    mut v_t_2509_: *mut LeanObject,
    mut v_k_2510_: u64,
) -> *mut LeanObject {
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    v___x_2511_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_t_2509_, v_k_2510_);
    return v___x_2511_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___boxed(
    mut v_00_u03b4_2512_: *mut LeanObject,
    mut v_t_2513_: *mut LeanObject,
    mut v_k_2514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_boxed_2515_: u64 = 0;
    let mut v_res_2516_: *mut LeanObject = core::ptr::null_mut();
    v_k_boxed_2515_ = lean_unbox_uint64(v_k_2514_);
    lean_dec_ref(v_k_2514_);
    v_res_2516_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(v_00_u03b4_2512_, v_t_2513_, v_k_boxed_2515_);
    lean_dec(v_t_2513_);
    return v_res_2516_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(
    mut v_00_u03b2_2517_: *mut LeanObject,
    mut v_k_2518_: u64,
    mut v_t_2519_: *mut LeanObject,
    mut v_h_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    v___x_2521_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_2518_, v_t_2519_);
    return v___x_2521_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___boxed(
    mut v_00_u03b2_2522_: *mut LeanObject,
    mut v_k_2523_: *mut LeanObject,
    mut v_t_2524_: *mut LeanObject,
    mut v_h_2525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_boxed_2526_: u64 = 0;
    let mut v_res_2527_: *mut LeanObject = core::ptr::null_mut();
    v_k_boxed_2526_ = lean_unbox_uint64(v_k_2523_);
    lean_dec_ref(v_k_2523_);
    v_res_2527_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(v_00_u03b2_2522_, v_k_boxed_2526_, v_t_2524_, v_h_2525_);
    return v_res_2527_;
}
pub unsafe fn l_Std_CancellationContext_cancel___lam__0(
    mut v_id_2528_: u64,
    mut v_reason_2529_: *mut LeanObject,
    mut v___y_2530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    v___x_2532_ = lean_st_ref_get(v___y_2530_);
    v___x_2533_ =
        l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(
            v___x_2532_,
            v_id_2528_,
            v_reason_2529_,
        );
    v___x_2534_ = lean_st_ref_set(v___y_2530_, v___x_2533_);
    return v___x_2534_;
}
pub unsafe fn l_Std_CancellationContext_cancel___lam__0___boxed(
    mut v_id_2535_: *mut LeanObject,
    mut v_reason_2536_: *mut LeanObject,
    mut v___y_2537_: *mut LeanObject,
    mut v___y_2538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_boxed_2539_: u64 = 0;
    let mut v_res_2540_: *mut LeanObject = core::ptr::null_mut();
    v_id_boxed_2539_ = lean_unbox_uint64(v_id_2535_);
    lean_dec_ref(v_id_2535_);
    v_res_2540_ =
        l_Std_CancellationContext_cancel___lam__0(v_id_boxed_2539_, v_reason_2536_, v___y_2537_);
    lean_dec(v___y_2537_);
    return v_res_2540_;
}
pub unsafe fn l_Std_CancellationContext_cancel(
    mut v_x_2541_: *mut LeanObject,
    mut v_reason_2542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_state_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_token_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_2546_: u64 = 0;
    let mut v___x_2547_: u8 = 0;
    v_state_2544_ = lean_ctor_get(v_x_2541_, 0);
    lean_inc_ref(v_state_2544_);
    v_token_2545_ = lean_ctor_get(v_x_2541_, 1);
    lean_inc_ref(v_token_2545_);
    v_id_2546_ = lean_ctor_get_uint64(
        v_x_2541_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    lean_dec_ref(v_x_2541_);
    v___x_2547_ = l_Std_CancellationToken_isCancelled(v_token_2545_);
    if v___x_2547_ == 0 {
        let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2549_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
        v___x_2548_ = lean_box_uint64(v_id_2546_);
        v___f_2549_ = lean_alloc_closure(
            l_Std_CancellationContext_cancel___lam__0___boxed as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_2549_, 0, v___x_2548_);
        lean_closure_set(v___f_2549_, 1, v_reason_2542_);
        v___x_2550_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(
            v_state_2544_,
            v___f_2549_,
        );
        return v___x_2550_;
    } else {
        let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_state_2544_);
        lean_dec(v_reason_2542_);
        v___x_2551_ = lean_box(0);
        return v___x_2551_;
    }
}
pub unsafe fn l_Std_CancellationContext_cancel___boxed(
    mut v_x_2552_: *mut LeanObject,
    mut v_reason_2553_: *mut LeanObject,
    mut v_a_2554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2555_: *mut LeanObject = core::ptr::null_mut();
    v_res_2555_ = l_Std_CancellationContext_cancel(v_x_2552_, v_reason_2553_);
    return v_res_2555_;
}
pub unsafe fn l_Std_CancellationContext_isCancelled(mut v_x_2556_: *mut LeanObject) -> u8 {
    let mut v_token_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: u8 = 0;
    v_token_2558_ = lean_ctor_get(v_x_2556_, 1);
    lean_inc_ref(v_token_2558_);
    lean_dec_ref(v_x_2556_);
    v___x_2559_ = l_Std_CancellationToken_isCancelled(v_token_2558_);
    return v___x_2559_;
}
pub unsafe fn l_Std_CancellationContext_isCancelled___boxed(
    mut v_x_2560_: *mut LeanObject,
    mut v_a_2561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2562_: u8 = 0;
    let mut v_r_2563_: *mut LeanObject = core::ptr::null_mut();
    v_res_2562_ = l_Std_CancellationContext_isCancelled(v_x_2560_);
    v_r_2563_ = lean_box((v_res_2562_) as usize);
    return v_r_2563_;
}
pub unsafe fn l_Std_CancellationContext_getCancellationReason(
    mut v_x_2564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_token_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    v_token_2566_ = lean_ctor_get(v_x_2564_, 1);
    lean_inc_ref(v_token_2566_);
    lean_dec_ref(v_x_2564_);
    v___x_2567_ = l_Std_CancellationToken_getCancellationReason(v_token_2566_);
    return v___x_2567_;
}
pub unsafe fn l_Std_CancellationContext_getCancellationReason___boxed(
    mut v_x_2568_: *mut LeanObject,
    mut v_a_2569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2570_: *mut LeanObject = core::ptr::null_mut();
    v_res_2570_ = l_Std_CancellationContext_getCancellationReason(v_x_2568_);
    return v_res_2570_;
}
pub unsafe fn l_Std_CancellationContext_done(mut v_x_2571_: *mut LeanObject) -> *mut LeanObject {
    let mut v_token_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    v_token_2573_ = lean_ctor_get(v_x_2571_, 1);
    lean_inc_ref(v_token_2573_);
    lean_dec_ref(v_x_2571_);
    v___x_2574_ = l_Std_CancellationToken_wait(v_token_2573_);
    return v___x_2574_;
}
pub unsafe fn l_Std_CancellationContext_done___boxed(
    mut v_x_2575_: *mut LeanObject,
    mut v_a_2576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2577_: *mut LeanObject = core::ptr::null_mut();
    v_res_2577_ = l_Std_CancellationContext_done(v_x_2575_);
    return v_res_2577_;
}
pub unsafe fn l_Std_CancellationContext_doneSelector(
    mut v_x_2578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_token_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    v_token_2579_ = lean_ctor_get(v_x_2578_, 1);
    lean_inc_ref(v_token_2579_);
    lean_dec_ref(v_x_2578_);
    v___x_2580_ = l_Std_CancellationToken_selector(v_token_2579_);
    return v___x_2580_;
}
pub unsafe fn l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(
    mut v_state_2581_: *mut LeanObject,
    mut v_id_2582_: u64,
) -> *mut LeanObject {
    let mut v_tokens_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    v_tokens_2583_ = lean_ctor_get(v_state_2581_, 0);
    v___x_2584_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_tokens_2583_, v_id_2582_);
    if lean_obj_tag(v___x_2584_) == 0 {
        let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
        v___x_2585_ = lean_unsigned_to_nat(0);
        return v___x_2585_;
    } else {
        let mut v_val_2586_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_2587_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2590_: u8 = 0;
        v_val_2586_ = lean_ctor_get(v___x_2584_, 0);
        lean_inc(v_val_2586_);
        lean_dec_ref_known(v___x_2584_, 1);
        v_snd_2587_ = lean_ctor_get(v_val_2586_, 1);
        lean_inc(v_snd_2587_);
        lean_dec(v_val_2586_);
        v___x_2588_ = lean_unsigned_to_nat(0);
        v___x_2589_ = lean_array_get_size(v_snd_2587_);
        v___x_2590_ = lean_nat_dec_lt(v___x_2588_, v___x_2589_);
        if v___x_2590_ == 0 {
            let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_snd_2587_);
            v___x_2591_ = lean_unsigned_to_nat(1);
            return v___x_2591_;
        } else {
            let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2593_: u8 = 0;
            v___x_2592_ = lean_unsigned_to_nat(1);
            v___x_2593_ = lean_nat_dec_le(v___x_2589_, v___x_2589_);
            if v___x_2593_ == 0 {
                if v___x_2590_ == 0 {
                    lean_dec(v_snd_2587_);
                    return v___x_2592_;
                } else {
                    let mut v___x_2594_: usize = 0;
                    let mut v___x_2595_: usize = 0;
                    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2594_ = 0usize;
                    v___x_2595_ = lean_usize_of_nat(v___x_2589_);
                    v___x_2596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_2581_, v_snd_2587_, v___x_2594_, v___x_2595_, v___x_2588_);
                    lean_dec(v_snd_2587_);
                    v___x_2597_ = lean_nat_add(v___x_2592_, v___x_2596_);
                    lean_dec(v___x_2596_);
                    return v___x_2597_;
                }
            } else {
                let mut v___x_2598_: usize = 0;
                let mut v___x_2599_: usize = 0;
                let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
                v___x_2598_ = 0usize;
                v___x_2599_ = lean_usize_of_nat(v___x_2589_);
                v___x_2600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_2581_, v_snd_2587_, v___x_2598_, v___x_2599_, v___x_2588_);
                lean_dec(v_snd_2587_);
                v___x_2601_ = lean_nat_add(v___x_2592_, v___x_2600_);
                lean_dec(v___x_2600_);
                return v___x_2601_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(
    mut v_state_2602_: *mut LeanObject,
    mut v_as_2603_: *mut LeanObject,
    mut v_i_2604_: usize,
    mut v_stop_2605_: usize,
    mut v_b_2606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2607_: u8 = 0;
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: u64 = 0;
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: usize = 0;
    let mut v___x_2613_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2607_ = lean_usize_dec_eq(v_i_2604_, v_stop_2605_);
                if v___x_2607_ == 0 {
                    v___x_2608_ = lean_array_uget_borrowed(v_as_2603_, v_i_2604_);
                    v___x_2609_ = lean_unbox_uint64(v___x_2608_);
                    v___x_2610_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(v_state_2602_, v___x_2609_);
                    v___x_2611_ = lean_nat_add(v_b_2606_, v___x_2610_);
                    lean_dec(v___x_2610_);
                    lean_dec(v_b_2606_);
                    v___x_2612_ = 1usize;
                    v___x_2613_ = lean_usize_add(v_i_2604_, v___x_2612_);
                    v_i_2604_ = v___x_2613_;
                    v_b_2606_ = v___x_2611_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2606_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0___boxed(
    mut v_state_2615_: *mut LeanObject,
    mut v_as_2616_: *mut LeanObject,
    mut v_i_2617_: *mut LeanObject,
    mut v_stop_2618_: *mut LeanObject,
    mut v_b_2619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2620_: usize = 0;
    let mut v_stop_boxed_2621_: usize = 0;
    let mut v_res_2622_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2620_ = lean_unbox_usize(v_i_2617_);
    lean_dec(v_i_2617_);
    v_stop_boxed_2621_ = lean_unbox_usize(v_stop_2618_);
    lean_dec(v_stop_2618_);
    v_res_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_2615_, v_as_2616_, v_i_boxed_2620_, v_stop_boxed_2621_, v_b_2619_);
    lean_dec_ref(v_as_2616_);
    lean_dec_ref(v_state_2615_);
    return v_res_2622_;
}
pub unsafe fn l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec___boxed(
    mut v_state_2623_: *mut LeanObject,
    mut v_id_2624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_boxed_2625_: u64 = 0;
    let mut v_res_2626_: *mut LeanObject = core::ptr::null_mut();
    v_id_boxed_2625_ = lean_unbox_uint64(v_id_2624_);
    lean_dec_ref(v_id_2624_);
    v_res_2626_ =
        l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(
            v_state_2623_,
            v_id_boxed_2625_,
        );
    lean_dec_ref(v_state_2623_);
    return v_res_2626_;
}
pub unsafe fn l_Std_CancellationContext_countAliveTokens___lam__0(
    mut v_id_2627_: u64,
    mut v___y_2628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    v___x_2630_ = lean_st_ref_get(v___y_2628_);
    v___x_2631_ =
        l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(
            v___x_2630_,
            v_id_2627_,
        );
    lean_dec(v___x_2630_);
    return v___x_2631_;
}
pub unsafe fn l_Std_CancellationContext_countAliveTokens___lam__0___boxed(
    mut v_id_2632_: *mut LeanObject,
    mut v___y_2633_: *mut LeanObject,
    mut v___y_2634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_boxed_2635_: u64 = 0;
    let mut v_res_2636_: *mut LeanObject = core::ptr::null_mut();
    v_id_boxed_2635_ = lean_unbox_uint64(v_id_2632_);
    lean_dec_ref(v_id_2632_);
    v_res_2636_ =
        l_Std_CancellationContext_countAliveTokens___lam__0(v_id_boxed_2635_, v___y_2633_);
    lean_dec(v___y_2633_);
    return v_res_2636_;
}
pub unsafe fn l_Std_CancellationContext_countAliveTokens(
    mut v_x_2637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_state_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_2640_: u64 = 0;
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    v_state_2639_ = lean_ctor_get(v_x_2637_, 0);
    lean_inc_ref(v_state_2639_);
    v_id_2640_ = lean_ctor_get_uint64(
        v_x_2637_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    lean_dec_ref(v_x_2637_);
    v___x_2641_ = lean_box_uint64(v_id_2640_);
    v___f_2642_ = lean_alloc_closure(
        l_Std_CancellationContext_countAliveTokens___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2642_, 0, v___x_2641_);
    v___x_2643_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(
        v_state_2639_,
        v___f_2642_,
    );
    return v___x_2643_;
}
pub unsafe fn l_Std_CancellationContext_countAliveTokens___boxed(
    mut v_x_2644_: *mut LeanObject,
    mut v_a_2645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2646_: *mut LeanObject = core::ptr::null_mut();
    v_res_2646_ = l_Std_CancellationContext_countAliveTokens(v_x_2644_);
    return v_res_2646_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sync_CancellationContext(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sync_CancellationToken(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_UInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_CancellationContext(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sync_CancellationContext(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sync_CancellationToken(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Ord_UInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_CancellationContext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sync_CancellationContext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sync_CancellationContext(builtin);
}
