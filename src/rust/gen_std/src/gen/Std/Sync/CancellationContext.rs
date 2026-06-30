// Lean compiler output
// Module: Std.Sync.CancellationContext
// Imports: Std.Sync.CancellationToken Init.Data.Ord.UInt
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget_borrowed,
    lean_io_basemutex_lock, lean_io_basemutex_unlock, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_mul, lean_st_ref_get, lean_st_ref_set, lean_uint64_add,
    lean_uint64_dec_eq, lean_uint64_dec_lt, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt,
    lean_usize_of_nat,
};
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
pub static l_Std_CancellationContext_new___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_CancellationContext_new___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationContext_new___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(
    mut v_k_1324_: u64,
    mut v_v_1325_: *mut leanh::LeanObject,
    mut v_t_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1334_: u8 = 0;
    let mut v___x_1335_: u64 = 0;
    let mut v___x_1336_: u8 = 0;
    let mut v___x_1337_: u64 = 0;
    let mut v___x_1338_: u8 = 0;
    let mut v_impl_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: u8 = 0;
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1357_: u8 = 0;
    let mut v_size_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: u8 = 0;
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1394_: u8 = 0;
    let mut v_unused_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1411_: u8 = 0;
    let mut v_unused_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1418_: u8 = 0;
    let mut v_unused_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v_k_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1435_: u8 = 0;
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1446_: u8 = 0;
    let mut v_unused_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1450_: u8 = 0;
    let mut v_unused_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1458_: u8 = 0;
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1466_: u8 = 0;
    let mut v_unused_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: u8 = 0;
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1496_: u8 = 0;
    let mut v_size_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: u8 = 0;
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1508_: u8 = 0;
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1534_: u8 = 0;
    let mut v_unused_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1548_: u8 = 0;
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1552_: u8 = 0;
    let mut v_unused_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1559_: u8 = 0;
    let mut v_unused_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1571_: u8 = 0;
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1579_: u8 = 0;
    let mut v_unused_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1587_: u8 = 0;
    let mut v_k_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1592_: u8 = 0;
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut v_unused_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1607_: u8 = 0;
    let mut v_unused_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1615_: u8 = 0;
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1326_) == 0 {
                    v_size_1327_ = leanh::lean_ctor_get(v_t_1326_, 0);
                    v_k_1328_ = leanh::lean_ctor_get(v_t_1326_, 1);
                    v_v_1329_ = leanh::lean_ctor_get(v_t_1326_, 2);
                    v_l_1330_ = leanh::lean_ctor_get(v_t_1326_, 3);
                    v_r_1331_ = leanh::lean_ctor_get(v_t_1326_, 4);
                    v_isSharedCheck_1615_ = (!leanh::lean_is_exclusive(v_t_1326_)) as u8;
                    if v_isSharedCheck_1615_ == 0 {
                        v___x_1333_ = v_t_1326_;
                        v_isShared_1334_ = v_isSharedCheck_1615_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_1331_);
                        leanh::lean_inc(v_l_1330_);
                        leanh::lean_inc(v_v_1329_);
                        leanh::lean_inc(v_k_1328_);
                        leanh::lean_inc(v_size_1327_);
                        leanh::lean_dec(v_t_1326_);
                        v___x_1333_ = leanh::lean_box(0);
                        v_isShared_1334_ = v_isSharedCheck_1615_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1616_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1617_ = leanh::lean_box_uint64(v_k_1324_);
                    v___x_1618_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_1618_, 0, v___x_1616_);
                    leanh::lean_ctor_set(v___x_1618_, 1, v___x_1617_);
                    leanh::lean_ctor_set(v___x_1618_, 2, v_v_1325_);
                    leanh::lean_ctor_set(v___x_1618_, 3, v_t_1326_);
                    leanh::lean_ctor_set(v___x_1618_, 4, v_t_1326_);
                    return v___x_1618_;
                }
            }
            1 => {
                v___x_1335_ = leanh::lean_unbox_uint64(v_k_1328_);
                v___x_1336_ = lean_uint64_dec_lt(v_k_1324_, v___x_1335_);
                if v___x_1336_ == 0 {
                    v___x_1337_ = leanh::lean_unbox_uint64(v_k_1328_);
                    v___x_1338_ = lean_uint64_dec_eq(v_k_1324_, v___x_1337_);
                    if v___x_1338_ == 0 {
                        leanh::lean_dec(v_size_1327_);
                        v_impl_1339_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_k_1324_, v_v_1325_, v_r_1331_);
                        v___x_1340_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_l_1330_) == 0 {
                            v_size_1341_ = leanh::lean_ctor_get(v_l_1330_, 0);
                            v_size_1342_ = leanh::lean_ctor_get(v_impl_1339_, 0);
                            leanh::lean_inc(v_size_1342_);
                            v_k_1343_ = leanh::lean_ctor_get(v_impl_1339_, 1);
                            leanh::lean_inc(v_k_1343_);
                            v_v_1344_ = leanh::lean_ctor_get(v_impl_1339_, 2);
                            leanh::lean_inc(v_v_1344_);
                            v_l_1345_ = leanh::lean_ctor_get(v_impl_1339_, 3);
                            leanh::lean_inc(v_l_1345_);
                            v_r_1346_ = leanh::lean_ctor_get(v_impl_1339_, 4);
                            leanh::lean_inc(v_r_1346_);
                            v___x_1347_ = leanh::lean_unsigned_to_nat(3);
                            v___x_1348_ = lean_nat_mul(v___x_1347_, v_size_1341_);
                            v___x_1349_ = lean_nat_dec_lt(v___x_1348_, v_size_1342_);
                            leanh::lean_dec(v___x_1348_);
                            if v___x_1349_ == 0 {
                                leanh::lean_dec(v_r_1346_);
                                leanh::lean_dec(v_l_1345_);
                                leanh::lean_dec(v_v_1344_);
                                leanh::lean_dec(v_k_1343_);
                                v___x_1350_ = lean_nat_add(v___x_1340_, v_size_1341_);
                                v___x_1351_ = lean_nat_add(v___x_1350_, v_size_1342_);
                                leanh::lean_dec(v_size_1342_);
                                leanh::lean_dec(v___x_1350_);
                                if v_isShared_1334_ == 0 {
                                    leanh::lean_ctor_set(v___x_1333_, 4, v_impl_1339_);
                                    leanh::lean_ctor_set(v___x_1333_, 0, v___x_1351_);
                                    v___x_1353_ = v___x_1333_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1354_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1354_,
                                        0,
                                        v___x_1351_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1354_,
                                        1,
                                        v_k_1328_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1354_,
                                        2,
                                        v_v_1329_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1354_,
                                        3,
                                        v_l_1330_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1354_,
                                        4,
                                        v_impl_1339_,
                                    );
                                    v___x_1353_ = v_reuseFailAlloc_1354_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1418_ =
                                    (!leanh::lean_is_exclusive(v_impl_1339_)) as u8;
                                if v_isSharedCheck_1418_ == 0 {
                                    v_unused_1419_ = leanh::lean_ctor_get(v_impl_1339_, 4);
                                    leanh::lean_dec(v_unused_1419_);
                                    v_unused_1420_ = leanh::lean_ctor_get(v_impl_1339_, 3);
                                    leanh::lean_dec(v_unused_1420_);
                                    v_unused_1421_ = leanh::lean_ctor_get(v_impl_1339_, 2);
                                    leanh::lean_dec(v_unused_1421_);
                                    v_unused_1422_ = leanh::lean_ctor_get(v_impl_1339_, 1);
                                    leanh::lean_dec(v_unused_1422_);
                                    v_unused_1423_ = leanh::lean_ctor_get(v_impl_1339_, 0);
                                    leanh::lean_dec(v_unused_1423_);
                                    v___x_1356_ = v_impl_1339_;
                                    v_isShared_1357_ = v_isSharedCheck_1418_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_1339_);
                                    v___x_1356_ = leanh::lean_box(0);
                                    v_isShared_1357_ = v_isSharedCheck_1418_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1424_ = leanh::lean_ctor_get(v_impl_1339_, 3);
                            leanh::lean_inc(v_l_1424_);
                            if leanh::lean_obj_tag(v_l_1424_) == 0 {
                                v_r_1425_ = leanh::lean_ctor_get(v_impl_1339_, 4);
                                v_k_1426_ = leanh::lean_ctor_get(v_impl_1339_, 1);
                                v_v_1427_ = leanh::lean_ctor_get(v_impl_1339_, 2);
                                v_isSharedCheck_1450_ =
                                    (!leanh::lean_is_exclusive(v_impl_1339_)) as u8;
                                if v_isSharedCheck_1450_ == 0 {
                                    v_unused_1451_ = leanh::lean_ctor_get(v_impl_1339_, 3);
                                    leanh::lean_dec(v_unused_1451_);
                                    v_unused_1452_ = leanh::lean_ctor_get(v_impl_1339_, 0);
                                    leanh::lean_dec(v_unused_1452_);
                                    v___x_1429_ = v_impl_1339_;
                                    v_isShared_1430_ = v_isSharedCheck_1450_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_1425_);
                                    leanh::lean_inc(v_v_1427_);
                                    leanh::lean_inc(v_k_1426_);
                                    leanh::lean_dec(v_impl_1339_);
                                    v___x_1429_ = leanh::lean_box(0);
                                    v_isShared_1430_ = v_isSharedCheck_1450_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1453_ = leanh::lean_ctor_get(v_impl_1339_, 4);
                                leanh::lean_inc(v_r_1453_);
                                if leanh::lean_obj_tag(v_r_1453_) == 0 {
                                    v_k_1454_ = leanh::lean_ctor_get(v_impl_1339_, 1);
                                    v_v_1455_ = leanh::lean_ctor_get(v_impl_1339_, 2);
                                    v_isSharedCheck_1466_ =
                                        (!leanh::lean_is_exclusive(v_impl_1339_)) as u8;
                                    if v_isSharedCheck_1466_ == 0 {
                                        v_unused_1467_ =
                                            leanh::lean_ctor_get(v_impl_1339_, 4);
                                        leanh::lean_dec(v_unused_1467_);
                                        v_unused_1468_ =
                                            leanh::lean_ctor_get(v_impl_1339_, 3);
                                        leanh::lean_dec(v_unused_1468_);
                                        v_unused_1469_ =
                                            leanh::lean_ctor_get(v_impl_1339_, 0);
                                        leanh::lean_dec(v_unused_1469_);
                                        v___x_1457_ = v_impl_1339_;
                                        v_isShared_1458_ = v_isSharedCheck_1466_;
                                        state = 18;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_1455_);
                                        leanh::lean_inc(v_k_1454_);
                                        leanh::lean_dec(v_impl_1339_);
                                        v___x_1457_ = leanh::lean_box(0);
                                        v_isShared_1458_ = v_isSharedCheck_1466_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_1470_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1334_ == 0 {
                                        leanh::lean_ctor_set(v___x_1333_, 4, v_impl_1339_);
                                        leanh::lean_ctor_set(v___x_1333_, 3, v_r_1453_);
                                        leanh::lean_ctor_set(v___x_1333_, 0, v___x_1470_);
                                        v___x_1472_ = v___x_1333_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1473_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1473_,
                                            0,
                                            v___x_1470_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1473_,
                                            1,
                                            v_k_1328_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1473_,
                                            2,
                                            v_v_1329_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1473_,
                                            3,
                                            v_r_1453_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1473_,
                                            4,
                                            v_impl_1339_,
                                        );
                                        v___x_1472_ = v_reuseFailAlloc_1473_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_v_1329_);
                        leanh::lean_dec(v_k_1328_);
                        v___x_1474_ = leanh::lean_box_uint64(v_k_1324_);
                        if v_isShared_1334_ == 0 {
                            leanh::lean_ctor_set(v___x_1333_, 2, v_v_1325_);
                            leanh::lean_ctor_set(v___x_1333_, 1, v___x_1474_);
                            v___x_1476_ = v___x_1333_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1477_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_size_1327_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1477_, 1, v___x_1474_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_v_1325_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1477_, 3, v_l_1330_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1477_, 4, v_r_1331_);
                            v___x_1476_ = v_reuseFailAlloc_1477_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_size_1327_);
                    v_impl_1478_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_k_1324_, v_v_1325_, v_l_1330_);
                    v___x_1479_ = leanh::lean_unsigned_to_nat(1);
                    if leanh::lean_obj_tag(v_r_1331_) == 0 {
                        v_size_1480_ = leanh::lean_ctor_get(v_r_1331_, 0);
                        v_size_1481_ = leanh::lean_ctor_get(v_impl_1478_, 0);
                        leanh::lean_inc(v_size_1481_);
                        v_k_1482_ = leanh::lean_ctor_get(v_impl_1478_, 1);
                        leanh::lean_inc(v_k_1482_);
                        v_v_1483_ = leanh::lean_ctor_get(v_impl_1478_, 2);
                        leanh::lean_inc(v_v_1483_);
                        v_l_1484_ = leanh::lean_ctor_get(v_impl_1478_, 3);
                        leanh::lean_inc(v_l_1484_);
                        v_r_1485_ = leanh::lean_ctor_get(v_impl_1478_, 4);
                        leanh::lean_inc(v_r_1485_);
                        v___x_1486_ = leanh::lean_unsigned_to_nat(3);
                        v___x_1487_ = lean_nat_mul(v___x_1486_, v_size_1480_);
                        v___x_1488_ = lean_nat_dec_lt(v___x_1487_, v_size_1481_);
                        leanh::lean_dec(v___x_1487_);
                        if v___x_1488_ == 0 {
                            leanh::lean_dec(v_r_1485_);
                            leanh::lean_dec(v_l_1484_);
                            leanh::lean_dec(v_v_1483_);
                            leanh::lean_dec(v_k_1482_);
                            v___x_1489_ = lean_nat_add(v___x_1479_, v_size_1481_);
                            leanh::lean_dec(v_size_1481_);
                            v___x_1490_ = lean_nat_add(v___x_1489_, v_size_1480_);
                            leanh::lean_dec(v___x_1489_);
                            if v_isShared_1334_ == 0 {
                                leanh::lean_ctor_set(v___x_1333_, 3, v_impl_1478_);
                                leanh::lean_ctor_set(v___x_1333_, 0, v___x_1490_);
                                v___x_1492_ = v___x_1333_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_1493_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_k_1328_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 2, v_v_1329_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1493_,
                                    3,
                                    v_impl_1478_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 4, v_r_1331_);
                                v___x_1492_ = v_reuseFailAlloc_1493_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_1559_ =
                                (!leanh::lean_is_exclusive(v_impl_1478_)) as u8;
                            if v_isSharedCheck_1559_ == 0 {
                                v_unused_1560_ = leanh::lean_ctor_get(v_impl_1478_, 4);
                                leanh::lean_dec(v_unused_1560_);
                                v_unused_1561_ = leanh::lean_ctor_get(v_impl_1478_, 3);
                                leanh::lean_dec(v_unused_1561_);
                                v_unused_1562_ = leanh::lean_ctor_get(v_impl_1478_, 2);
                                leanh::lean_dec(v_unused_1562_);
                                v_unused_1563_ = leanh::lean_ctor_get(v_impl_1478_, 1);
                                leanh::lean_dec(v_unused_1563_);
                                v_unused_1564_ = leanh::lean_ctor_get(v_impl_1478_, 0);
                                leanh::lean_dec(v_unused_1564_);
                                v___x_1495_ = v_impl_1478_;
                                v_isShared_1496_ = v_isSharedCheck_1559_;
                                state = 24;
                                continue;
                            } else {
                                leanh::lean_dec(v_impl_1478_);
                                v___x_1495_ = leanh::lean_box(0);
                                v_isShared_1496_ = v_isSharedCheck_1559_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_1565_ = leanh::lean_ctor_get(v_impl_1478_, 3);
                        leanh::lean_inc(v_l_1565_);
                        if leanh::lean_obj_tag(v_l_1565_) == 0 {
                            v_r_1566_ = leanh::lean_ctor_get(v_impl_1478_, 4);
                            v_k_1567_ = leanh::lean_ctor_get(v_impl_1478_, 1);
                            v_v_1568_ = leanh::lean_ctor_get(v_impl_1478_, 2);
                            v_isSharedCheck_1579_ =
                                (!leanh::lean_is_exclusive(v_impl_1478_)) as u8;
                            if v_isSharedCheck_1579_ == 0 {
                                v_unused_1580_ = leanh::lean_ctor_get(v_impl_1478_, 3);
                                leanh::lean_dec(v_unused_1580_);
                                v_unused_1581_ = leanh::lean_ctor_get(v_impl_1478_, 0);
                                leanh::lean_dec(v_unused_1581_);
                                v___x_1570_ = v_impl_1478_;
                                v_isShared_1571_ = v_isSharedCheck_1579_;
                                state = 34;
                                continue;
                            } else {
                                leanh::lean_inc(v_r_1566_);
                                leanh::lean_inc(v_v_1568_);
                                leanh::lean_inc(v_k_1567_);
                                leanh::lean_dec(v_impl_1478_);
                                v___x_1570_ = leanh::lean_box(0);
                                v_isShared_1571_ = v_isSharedCheck_1579_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_1582_ = leanh::lean_ctor_get(v_impl_1478_, 4);
                            leanh::lean_inc(v_r_1582_);
                            if leanh::lean_obj_tag(v_r_1582_) == 0 {
                                v_k_1583_ = leanh::lean_ctor_get(v_impl_1478_, 1);
                                v_v_1584_ = leanh::lean_ctor_get(v_impl_1478_, 2);
                                v_isSharedCheck_1607_ =
                                    (!leanh::lean_is_exclusive(v_impl_1478_)) as u8;
                                if v_isSharedCheck_1607_ == 0 {
                                    v_unused_1608_ = leanh::lean_ctor_get(v_impl_1478_, 4);
                                    leanh::lean_dec(v_unused_1608_);
                                    v_unused_1609_ = leanh::lean_ctor_get(v_impl_1478_, 3);
                                    leanh::lean_dec(v_unused_1609_);
                                    v_unused_1610_ = leanh::lean_ctor_get(v_impl_1478_, 0);
                                    leanh::lean_dec(v_unused_1610_);
                                    v___x_1586_ = v_impl_1478_;
                                    v_isShared_1587_ = v_isSharedCheck_1607_;
                                    state = 37;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_v_1584_);
                                    leanh::lean_inc(v_k_1583_);
                                    leanh::lean_dec(v_impl_1478_);
                                    v___x_1586_ = leanh::lean_box(0);
                                    v_isShared_1587_ = v_isSharedCheck_1607_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_1611_ = leanh::lean_unsigned_to_nat(2);
                                if v_isShared_1334_ == 0 {
                                    leanh::lean_ctor_set(v___x_1333_, 4, v_r_1582_);
                                    leanh::lean_ctor_set(v___x_1333_, 3, v_impl_1478_);
                                    leanh::lean_ctor_set(v___x_1333_, 0, v___x_1611_);
                                    v___x_1613_ = v___x_1333_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1614_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1614_,
                                        0,
                                        v___x_1611_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1614_,
                                        1,
                                        v_k_1328_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1614_,
                                        2,
                                        v_v_1329_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1614_,
                                        3,
                                        v_impl_1478_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1614_,
                                        4,
                                        v_r_1582_,
                                    );
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
                v_size_1358_ = leanh::lean_ctor_get(v_l_1345_, 0);
                v_k_1359_ = leanh::lean_ctor_get(v_l_1345_, 1);
                v_v_1360_ = leanh::lean_ctor_get(v_l_1345_, 2);
                v_l_1361_ = leanh::lean_ctor_get(v_l_1345_, 3);
                v_r_1362_ = leanh::lean_ctor_get(v_l_1345_, 4);
                v_size_1363_ = leanh::lean_ctor_get(v_r_1346_, 0);
                v___x_1364_ = leanh::lean_unsigned_to_nat(2);
                v___x_1365_ = lean_nat_mul(v___x_1364_, v_size_1363_);
                v___x_1366_ = lean_nat_dec_lt(v_size_1358_, v___x_1365_);
                leanh::lean_dec(v___x_1365_);
                if v___x_1366_ == 0 {
                    leanh::lean_inc(v_r_1362_);
                    leanh::lean_inc(v_l_1361_);
                    leanh::lean_inc(v_v_1360_);
                    leanh::lean_inc(v_k_1359_);
                    v_isSharedCheck_1394_ = (!leanh::lean_is_exclusive(v_l_1345_)) as u8;
                    if v_isSharedCheck_1394_ == 0 {
                        v_unused_1395_ = leanh::lean_ctor_get(v_l_1345_, 4);
                        leanh::lean_dec(v_unused_1395_);
                        v_unused_1396_ = leanh::lean_ctor_get(v_l_1345_, 3);
                        leanh::lean_dec(v_unused_1396_);
                        v_unused_1397_ = leanh::lean_ctor_get(v_l_1345_, 2);
                        leanh::lean_dec(v_unused_1397_);
                        v_unused_1398_ = leanh::lean_ctor_get(v_l_1345_, 1);
                        leanh::lean_dec(v_unused_1398_);
                        v_unused_1399_ = leanh::lean_ctor_get(v_l_1345_, 0);
                        leanh::lean_dec(v_unused_1399_);
                        v___x_1368_ = v_l_1345_;
                        v_isShared_1369_ = v_isSharedCheck_1394_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_1345_);
                        v___x_1368_ = leanh::lean_box(0);
                        v_isShared_1369_ = v_isSharedCheck_1394_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1333_);
                    v___x_1400_ = lean_nat_add(v___x_1340_, v_size_1341_);
                    v___x_1401_ = lean_nat_add(v___x_1400_, v_size_1342_);
                    leanh::lean_dec(v_size_1342_);
                    v___x_1402_ = lean_nat_add(v___x_1400_, v_size_1358_);
                    leanh::lean_dec(v___x_1400_);
                    leanh::lean_inc_ref(v_l_1330_);
                    if v_isShared_1357_ == 0 {
                        leanh::lean_ctor_set(v___x_1356_, 4, v_l_1345_);
                        leanh::lean_ctor_set(v___x_1356_, 3, v_l_1330_);
                        leanh::lean_ctor_set(v___x_1356_, 2, v_v_1329_);
                        leanh::lean_ctor_set(v___x_1356_, 1, v_k_1328_);
                        leanh::lean_ctor_set(v___x_1356_, 0, v___x_1402_);
                        v___x_1404_ = v___x_1356_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1417_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1402_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1328_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1329_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_l_1330_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 4, v_l_1345_);
                        v___x_1404_ = v_reuseFailAlloc_1417_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1370_ = lean_nat_add(v___x_1340_, v_size_1341_);
                v___x_1371_ = lean_nat_add(v___x_1370_, v_size_1342_);
                leanh::lean_dec(v_size_1342_);
                if leanh::lean_obj_tag(v_l_1361_) == 0 {
                    v_size_1392_ = leanh::lean_ctor_get(v_l_1361_, 0);
                    leanh::lean_inc(v_size_1392_);
                    v___y_1384_ = v_size_1392_;
                    state = 8;
                    continue;
                } else {
                    v___x_1393_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1384_ = v___x_1393_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1376_ = lean_nat_add(v___y_1373_, v___y_1375_);
                leanh::lean_dec(v___y_1375_);
                leanh::lean_dec(v___y_1373_);
                if v_isShared_1369_ == 0 {
                    leanh::lean_ctor_set(v___x_1368_, 4, v_r_1346_);
                    leanh::lean_ctor_set(v___x_1368_, 3, v_r_1362_);
                    leanh::lean_ctor_set(v___x_1368_, 2, v_v_1344_);
                    leanh::lean_ctor_set(v___x_1368_, 1, v_k_1343_);
                    leanh::lean_ctor_set(v___x_1368_, 0, v___x_1376_);
                    v___x_1378_ = v___x_1368_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1382_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1376_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_k_1343_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1382_, 2, v_v_1344_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1382_, 3, v_r_1362_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1382_, 4, v_r_1346_);
                    v___x_1378_ = v_reuseFailAlloc_1382_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1357_ == 0 {
                    leanh::lean_ctor_set(v___x_1356_, 4, v___x_1378_);
                    leanh::lean_ctor_set(v___x_1356_, 3, v___y_1374_);
                    leanh::lean_ctor_set(v___x_1356_, 2, v_v_1360_);
                    leanh::lean_ctor_set(v___x_1356_, 1, v_k_1359_);
                    leanh::lean_ctor_set(v___x_1356_, 0, v___x_1371_);
                    v___x_1380_ = v___x_1356_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1381_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1371_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_k_1359_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1381_, 2, v_v_1360_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1381_, 3, v___y_1374_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1381_, 4, v___x_1378_);
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
                leanh::lean_dec(v___y_1384_);
                leanh::lean_dec(v___x_1370_);
                if v_isShared_1334_ == 0 {
                    leanh::lean_ctor_set(v___x_1333_, 4, v_l_1361_);
                    leanh::lean_ctor_set(v___x_1333_, 0, v___x_1385_);
                    v___x_1387_ = v___x_1333_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1391_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1385_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_k_1328_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_v_1329_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_l_1330_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 4, v_l_1361_);
                    v___x_1387_ = v_reuseFailAlloc_1391_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1388_ = lean_nat_add(v___x_1340_, v_size_1363_);
                if leanh::lean_obj_tag(v_r_1362_) == 0 {
                    v_size_1389_ = leanh::lean_ctor_get(v_r_1362_, 0);
                    leanh::lean_inc(v_size_1389_);
                    v___y_1373_ = v___x_1388_;
                    v___y_1374_ = v___x_1387_;
                    v___y_1375_ = v_size_1389_;
                    state = 5;
                    continue;
                } else {
                    v___x_1390_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1373_ = v___x_1388_;
                    v___y_1374_ = v___x_1387_;
                    v___y_1375_ = v___x_1390_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1411_ = (!leanh::lean_is_exclusive(v_l_1330_)) as u8;
                if v_isSharedCheck_1411_ == 0 {
                    v_unused_1412_ = leanh::lean_ctor_get(v_l_1330_, 4);
                    leanh::lean_dec(v_unused_1412_);
                    v_unused_1413_ = leanh::lean_ctor_get(v_l_1330_, 3);
                    leanh::lean_dec(v_unused_1413_);
                    v_unused_1414_ = leanh::lean_ctor_get(v_l_1330_, 2);
                    leanh::lean_dec(v_unused_1414_);
                    v_unused_1415_ = leanh::lean_ctor_get(v_l_1330_, 1);
                    leanh::lean_dec(v_unused_1415_);
                    v_unused_1416_ = leanh::lean_ctor_get(v_l_1330_, 0);
                    leanh::lean_dec(v_unused_1416_);
                    v___x_1406_ = v_l_1330_;
                    v_isShared_1407_ = v_isSharedCheck_1411_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_l_1330_);
                    v___x_1406_ = leanh::lean_box(0);
                    v_isShared_1407_ = v_isSharedCheck_1411_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1407_ == 0 {
                    leanh::lean_ctor_set(v___x_1406_, 4, v_r_1346_);
                    leanh::lean_ctor_set(v___x_1406_, 3, v___x_1404_);
                    leanh::lean_ctor_set(v___x_1406_, 2, v_v_1344_);
                    leanh::lean_ctor_set(v___x_1406_, 1, v_k_1343_);
                    leanh::lean_ctor_set(v___x_1406_, 0, v___x_1401_);
                    v___x_1409_ = v___x_1406_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1410_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_k_1343_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_v_1344_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 3, v___x_1404_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_r_1346_);
                    v___x_1409_ = v_reuseFailAlloc_1410_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1409_;
            }
            13 => {
                v_k_1431_ = leanh::lean_ctor_get(v_l_1424_, 1);
                v_v_1432_ = leanh::lean_ctor_get(v_l_1424_, 2);
                v_isSharedCheck_1446_ = (!leanh::lean_is_exclusive(v_l_1424_)) as u8;
                if v_isSharedCheck_1446_ == 0 {
                    v_unused_1447_ = leanh::lean_ctor_get(v_l_1424_, 4);
                    leanh::lean_dec(v_unused_1447_);
                    v_unused_1448_ = leanh::lean_ctor_get(v_l_1424_, 3);
                    leanh::lean_dec(v_unused_1448_);
                    v_unused_1449_ = leanh::lean_ctor_get(v_l_1424_, 0);
                    leanh::lean_dec(v_unused_1449_);
                    v___x_1434_ = v_l_1424_;
                    v_isShared_1435_ = v_isSharedCheck_1446_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_v_1432_);
                    leanh::lean_inc(v_k_1431_);
                    leanh::lean_dec(v_l_1424_);
                    v___x_1434_ = leanh::lean_box(0);
                    v_isShared_1435_ = v_isSharedCheck_1446_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_1436_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc_n(v_r_1425_, 2);
                if v_isShared_1435_ == 0 {
                    leanh::lean_ctor_set(v___x_1434_, 4, v_r_1425_);
                    leanh::lean_ctor_set(v___x_1434_, 3, v_r_1425_);
                    leanh::lean_ctor_set(v___x_1434_, 2, v_v_1329_);
                    leanh::lean_ctor_set(v___x_1434_, 1, v_k_1328_);
                    leanh::lean_ctor_set(v___x_1434_, 0, v___x_1340_);
                    v___x_1438_ = v___x_1434_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1445_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1340_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_k_1328_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_v_1329_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 3, v_r_1425_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 4, v_r_1425_);
                    v___x_1438_ = v_reuseFailAlloc_1445_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                leanh::lean_inc(v_r_1425_);
                if v_isShared_1430_ == 0 {
                    leanh::lean_ctor_set(v___x_1429_, 3, v_r_1425_);
                    leanh::lean_ctor_set(v___x_1429_, 0, v___x_1340_);
                    v___x_1440_ = v___x_1429_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1444_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1340_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_k_1426_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_v_1427_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 3, v_r_1425_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 4, v_r_1425_);
                    v___x_1440_ = v_reuseFailAlloc_1444_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_1334_ == 0 {
                    leanh::lean_ctor_set(v___x_1333_, 4, v___x_1440_);
                    leanh::lean_ctor_set(v___x_1333_, 3, v___x_1438_);
                    leanh::lean_ctor_set(v___x_1333_, 2, v_v_1432_);
                    leanh::lean_ctor_set(v___x_1333_, 1, v_k_1431_);
                    leanh::lean_ctor_set(v___x_1333_, 0, v___x_1436_);
                    v___x_1442_ = v___x_1333_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1443_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1436_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_k_1431_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_v_1432_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 3, v___x_1438_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 4, v___x_1440_);
                    v___x_1442_ = v_reuseFailAlloc_1443_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1442_;
            }
            18 => {
                v___x_1459_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_1458_ == 0 {
                    leanh::lean_ctor_set(v___x_1457_, 4, v_l_1424_);
                    leanh::lean_ctor_set(v___x_1457_, 2, v_v_1329_);
                    leanh::lean_ctor_set(v___x_1457_, 1, v_k_1328_);
                    leanh::lean_ctor_set(v___x_1457_, 0, v___x_1340_);
                    v___x_1461_ = v___x_1457_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1465_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1340_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_k_1328_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_v_1329_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 3, v_l_1424_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 4, v_l_1424_);
                    v___x_1461_ = v_reuseFailAlloc_1465_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1334_ == 0 {
                    leanh::lean_ctor_set(v___x_1333_, 4, v_r_1453_);
                    leanh::lean_ctor_set(v___x_1333_, 3, v___x_1461_);
                    leanh::lean_ctor_set(v___x_1333_, 2, v_v_1455_);
                    leanh::lean_ctor_set(v___x_1333_, 1, v_k_1454_);
                    leanh::lean_ctor_set(v___x_1333_, 0, v___x_1459_);
                    v___x_1463_ = v___x_1333_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1464_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1459_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_k_1454_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_v_1455_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 3, v___x_1461_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 4, v_r_1453_);
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
                v_size_1497_ = leanh::lean_ctor_get(v_l_1484_, 0);
                v_size_1498_ = leanh::lean_ctor_get(v_r_1485_, 0);
                v_k_1499_ = leanh::lean_ctor_get(v_r_1485_, 1);
                v_v_1500_ = leanh::lean_ctor_get(v_r_1485_, 2);
                v_l_1501_ = leanh::lean_ctor_get(v_r_1485_, 3);
                v_r_1502_ = leanh::lean_ctor_get(v_r_1485_, 4);
                v___x_1503_ = leanh::lean_unsigned_to_nat(2);
                v___x_1504_ = lean_nat_mul(v___x_1503_, v_size_1497_);
                v___x_1505_ = lean_nat_dec_lt(v_size_1498_, v___x_1504_);
                leanh::lean_dec(v___x_1504_);
                if v___x_1505_ == 0 {
                    leanh::lean_inc(v_r_1502_);
                    leanh::lean_inc(v_l_1501_);
                    leanh::lean_inc(v_v_1500_);
                    leanh::lean_inc(v_k_1499_);
                    v_isSharedCheck_1534_ = (!leanh::lean_is_exclusive(v_r_1485_)) as u8;
                    if v_isSharedCheck_1534_ == 0 {
                        v_unused_1535_ = leanh::lean_ctor_get(v_r_1485_, 4);
                        leanh::lean_dec(v_unused_1535_);
                        v_unused_1536_ = leanh::lean_ctor_get(v_r_1485_, 3);
                        leanh::lean_dec(v_unused_1536_);
                        v_unused_1537_ = leanh::lean_ctor_get(v_r_1485_, 2);
                        leanh::lean_dec(v_unused_1537_);
                        v_unused_1538_ = leanh::lean_ctor_get(v_r_1485_, 1);
                        leanh::lean_dec(v_unused_1538_);
                        v_unused_1539_ = leanh::lean_ctor_get(v_r_1485_, 0);
                        leanh::lean_dec(v_unused_1539_);
                        v___x_1507_ = v_r_1485_;
                        v_isShared_1508_ = v_isSharedCheck_1534_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_1485_);
                        v___x_1507_ = leanh::lean_box(0);
                        v_isShared_1508_ = v_isSharedCheck_1534_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1333_);
                    v___x_1540_ = lean_nat_add(v___x_1479_, v_size_1481_);
                    leanh::lean_dec(v_size_1481_);
                    v___x_1541_ = lean_nat_add(v___x_1540_, v_size_1480_);
                    leanh::lean_dec(v___x_1540_);
                    v___x_1542_ = lean_nat_add(v___x_1479_, v_size_1480_);
                    v___x_1543_ = lean_nat_add(v___x_1542_, v_size_1498_);
                    leanh::lean_dec(v___x_1542_);
                    leanh::lean_inc_ref(v_r_1331_);
                    if v_isShared_1496_ == 0 {
                        leanh::lean_ctor_set(v___x_1495_, 4, v_r_1331_);
                        leanh::lean_ctor_set(v___x_1495_, 3, v_r_1485_);
                        leanh::lean_ctor_set(v___x_1495_, 2, v_v_1329_);
                        leanh::lean_ctor_set(v___x_1495_, 1, v_k_1328_);
                        leanh::lean_ctor_set(v___x_1495_, 0, v___x_1543_);
                        v___x_1545_ = v___x_1495_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_1558_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1543_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1328_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1329_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_r_1485_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_r_1331_);
                        v___x_1545_ = v_reuseFailAlloc_1558_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1509_ = lean_nat_add(v___x_1479_, v_size_1481_);
                leanh::lean_dec(v_size_1481_);
                v___x_1510_ = lean_nat_add(v___x_1509_, v_size_1480_);
                leanh::lean_dec(v___x_1509_);
                v___x_1522_ = lean_nat_add(v___x_1479_, v_size_1497_);
                if leanh::lean_obj_tag(v_l_1501_) == 0 {
                    v_size_1532_ = leanh::lean_ctor_get(v_l_1501_, 0);
                    leanh::lean_inc(v_size_1532_);
                    v___y_1524_ = v_size_1532_;
                    state = 29;
                    continue;
                } else {
                    v___x_1533_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1524_ = v___x_1533_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_1515_ = lean_nat_add(v___y_1513_, v___y_1514_);
                leanh::lean_dec(v___y_1514_);
                leanh::lean_dec(v___y_1513_);
                if v_isShared_1508_ == 0 {
                    leanh::lean_ctor_set(v___x_1507_, 4, v_r_1331_);
                    leanh::lean_ctor_set(v___x_1507_, 3, v_r_1502_);
                    leanh::lean_ctor_set(v___x_1507_, 2, v_v_1329_);
                    leanh::lean_ctor_set(v___x_1507_, 1, v_k_1328_);
                    leanh::lean_ctor_set(v___x_1507_, 0, v___x_1515_);
                    v___x_1517_ = v___x_1507_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1521_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1515_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_k_1328_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_v_1329_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_r_1502_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 4, v_r_1331_);
                    v___x_1517_ = v_reuseFailAlloc_1521_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1496_ == 0 {
                    leanh::lean_ctor_set(v___x_1495_, 4, v___x_1517_);
                    leanh::lean_ctor_set(v___x_1495_, 3, v___y_1512_);
                    leanh::lean_ctor_set(v___x_1495_, 2, v_v_1500_);
                    leanh::lean_ctor_set(v___x_1495_, 1, v_k_1499_);
                    leanh::lean_ctor_set(v___x_1495_, 0, v___x_1510_);
                    v___x_1519_ = v___x_1495_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1520_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1510_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_k_1499_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_v_1500_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1520_, 3, v___y_1512_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1520_, 4, v___x_1517_);
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
                leanh::lean_dec(v___y_1524_);
                leanh::lean_dec(v___x_1522_);
                if v_isShared_1334_ == 0 {
                    leanh::lean_ctor_set(v___x_1333_, 4, v_l_1501_);
                    leanh::lean_ctor_set(v___x_1333_, 3, v_l_1484_);
                    leanh::lean_ctor_set(v___x_1333_, 2, v_v_1483_);
                    leanh::lean_ctor_set(v___x_1333_, 1, v_k_1482_);
                    leanh::lean_ctor_set(v___x_1333_, 0, v___x_1525_);
                    v___x_1527_ = v___x_1333_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1531_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1525_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_k_1482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_v_1483_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_l_1484_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_l_1501_);
                    v___x_1527_ = v_reuseFailAlloc_1531_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1528_ = lean_nat_add(v___x_1479_, v_size_1480_);
                if leanh::lean_obj_tag(v_r_1502_) == 0 {
                    v_size_1529_ = leanh::lean_ctor_get(v_r_1502_, 0);
                    leanh::lean_inc(v_size_1529_);
                    v___y_1512_ = v___x_1527_;
                    v___y_1513_ = v___x_1528_;
                    v___y_1514_ = v_size_1529_;
                    state = 26;
                    continue;
                } else {
                    v___x_1530_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1512_ = v___x_1527_;
                    v___y_1513_ = v___x_1528_;
                    v___y_1514_ = v___x_1530_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_1552_ = (!leanh::lean_is_exclusive(v_r_1331_)) as u8;
                if v_isSharedCheck_1552_ == 0 {
                    v_unused_1553_ = leanh::lean_ctor_get(v_r_1331_, 4);
                    leanh::lean_dec(v_unused_1553_);
                    v_unused_1554_ = leanh::lean_ctor_get(v_r_1331_, 3);
                    leanh::lean_dec(v_unused_1554_);
                    v_unused_1555_ = leanh::lean_ctor_get(v_r_1331_, 2);
                    leanh::lean_dec(v_unused_1555_);
                    v_unused_1556_ = leanh::lean_ctor_get(v_r_1331_, 1);
                    leanh::lean_dec(v_unused_1556_);
                    v_unused_1557_ = leanh::lean_ctor_get(v_r_1331_, 0);
                    leanh::lean_dec(v_unused_1557_);
                    v___x_1547_ = v_r_1331_;
                    v_isShared_1548_ = v_isSharedCheck_1552_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_dec(v_r_1331_);
                    v___x_1547_ = leanh::lean_box(0);
                    v_isShared_1548_ = v_isSharedCheck_1552_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1548_ == 0 {
                    leanh::lean_ctor_set(v___x_1547_, 4, v___x_1545_);
                    leanh::lean_ctor_set(v___x_1547_, 3, v_l_1484_);
                    leanh::lean_ctor_set(v___x_1547_, 2, v_v_1483_);
                    leanh::lean_ctor_set(v___x_1547_, 1, v_k_1482_);
                    leanh::lean_ctor_set(v___x_1547_, 0, v___x_1541_);
                    v___x_1550_ = v___x_1547_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1551_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1541_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_k_1482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1551_, 2, v_v_1483_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1551_, 3, v_l_1484_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1551_, 4, v___x_1545_);
                    v___x_1550_ = v_reuseFailAlloc_1551_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1550_;
            }
            34 => {
                v___x_1572_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc(v_r_1566_);
                if v_isShared_1571_ == 0 {
                    leanh::lean_ctor_set(v___x_1570_, 3, v_r_1566_);
                    leanh::lean_ctor_set(v___x_1570_, 2, v_v_1329_);
                    leanh::lean_ctor_set(v___x_1570_, 1, v_k_1328_);
                    leanh::lean_ctor_set(v___x_1570_, 0, v___x_1479_);
                    v___x_1574_ = v___x_1570_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1578_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1479_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_k_1328_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_v_1329_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 3, v_r_1566_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 4, v_r_1566_);
                    v___x_1574_ = v_reuseFailAlloc_1578_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_1334_ == 0 {
                    leanh::lean_ctor_set(v___x_1333_, 4, v___x_1574_);
                    leanh::lean_ctor_set(v___x_1333_, 3, v_l_1565_);
                    leanh::lean_ctor_set(v___x_1333_, 2, v_v_1568_);
                    leanh::lean_ctor_set(v___x_1333_, 1, v_k_1567_);
                    leanh::lean_ctor_set(v___x_1333_, 0, v___x_1572_);
                    v___x_1576_ = v___x_1333_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1577_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1572_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_k_1567_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_v_1568_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 3, v_l_1565_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 4, v___x_1574_);
                    v___x_1576_ = v_reuseFailAlloc_1577_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_1576_;
            }
            37 => {
                v_k_1588_ = leanh::lean_ctor_get(v_r_1582_, 1);
                v_v_1589_ = leanh::lean_ctor_get(v_r_1582_, 2);
                v_isSharedCheck_1603_ = (!leanh::lean_is_exclusive(v_r_1582_)) as u8;
                if v_isSharedCheck_1603_ == 0 {
                    v_unused_1604_ = leanh::lean_ctor_get(v_r_1582_, 4);
                    leanh::lean_dec(v_unused_1604_);
                    v_unused_1605_ = leanh::lean_ctor_get(v_r_1582_, 3);
                    leanh::lean_dec(v_unused_1605_);
                    v_unused_1606_ = leanh::lean_ctor_get(v_r_1582_, 0);
                    leanh::lean_dec(v_unused_1606_);
                    v___x_1591_ = v_r_1582_;
                    v_isShared_1592_ = v_isSharedCheck_1603_;
                    state = 38;
                    continue;
                } else {
                    leanh::lean_inc(v_v_1589_);
                    leanh::lean_inc(v_k_1588_);
                    leanh::lean_dec(v_r_1582_);
                    v___x_1591_ = leanh::lean_box(0);
                    v_isShared_1592_ = v_isSharedCheck_1603_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_1593_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_1592_ == 0 {
                    leanh::lean_ctor_set(v___x_1591_, 4, v_l_1565_);
                    leanh::lean_ctor_set(v___x_1591_, 3, v_l_1565_);
                    leanh::lean_ctor_set(v___x_1591_, 2, v_v_1584_);
                    leanh::lean_ctor_set(v___x_1591_, 1, v_k_1583_);
                    leanh::lean_ctor_set(v___x_1591_, 0, v___x_1479_);
                    v___x_1595_ = v___x_1591_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1479_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_k_1583_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_v_1584_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 3, v_l_1565_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 4, v_l_1565_);
                    v___x_1595_ = v_reuseFailAlloc_1602_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_1587_ == 0 {
                    leanh::lean_ctor_set(v___x_1586_, 4, v_l_1565_);
                    leanh::lean_ctor_set(v___x_1586_, 2, v_v_1329_);
                    leanh::lean_ctor_set(v___x_1586_, 1, v_k_1328_);
                    leanh::lean_ctor_set(v___x_1586_, 0, v___x_1479_);
                    v___x_1597_ = v___x_1586_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1601_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1479_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_k_1328_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_v_1329_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_l_1565_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_l_1565_);
                    v___x_1597_ = v_reuseFailAlloc_1601_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1334_ == 0 {
                    leanh::lean_ctor_set(v___x_1333_, 4, v___x_1597_);
                    leanh::lean_ctor_set(v___x_1333_, 3, v___x_1595_);
                    leanh::lean_ctor_set(v___x_1333_, 2, v_v_1589_);
                    leanh::lean_ctor_set(v___x_1333_, 1, v_k_1588_);
                    leanh::lean_ctor_set(v___x_1333_, 0, v___x_1593_);
                    v___x_1599_ = v___x_1333_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1600_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1593_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_k_1588_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_v_1589_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 3, v___x_1595_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 4, v___x_1597_);
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
    mut v_k_1619_: *mut leanh::LeanObject,
    mut v_v_1620_: *mut leanh::LeanObject,
    mut v_t_1621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_boxed_1622_: u64 = 0;
    let mut v_res_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_1622_ = leanh::lean_unbox_uint64(v_k_1619_);
    leanh::lean_dec_ref(v_k_1619_);
    v_res_1623_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(
            v_k_boxed_1622_,
            v_v_1620_,
            v_t_1621_,
        );
    return v_res_1623_;
}
pub unsafe fn l_Std_CancellationContext_new() -> *mut leanh::LeanObject {
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: u64 = 0;
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: u64 = 0;
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_Std_CancellationToken_new();
    v___x_1628_ = leanh::lean_box(1);
    v___x_1629_ = 0u64;
    v___x_1630_ = l_Std_CancellationContext_new___closed__0;
    leanh::lean_inc_ref(v___x_1627_);
    v___x_1631_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1631_, 0, v___x_1627_);
    leanh::lean_ctor_set(v___x_1631_, 1, v___x_1630_);
    v___x_1632_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(
            v___x_1629_,
            v___x_1631_,
            v___x_1628_,
        );
    v___x_1633_ = 1u64;
    v___x_1634_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_1634_, 0, v___x_1632_);
    leanh::lean_ctor_set_uint64(
        v___x_1634_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1633_,
    );
    v___x_1635_ = l_Std_Mutex_new___redArg(v___x_1634_);
    v___x_1636_ = leanh::lean_alloc_ctor(0, 2, (8) as u32);
    leanh::lean_ctor_set(v___x_1636_, 0, v___x_1635_);
    leanh::lean_ctor_set(v___x_1636_, 1, v___x_1627_);
    leanh::lean_ctor_set_uint64(
        v___x_1636_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_1629_,
    );
    return v___x_1636_;
}
pub unsafe fn l_Std_CancellationContext_new___boxed(
    mut v_a_1637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1638_ = l_Std_CancellationContext_new();
    return v_res_1638_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(
    mut v_00_u03b2_1639_: *mut leanh::LeanObject,
    mut v_k_1640_: u64,
    mut v_v_1641_: *mut leanh::LeanObject,
    mut v_t_1642_: *mut leanh::LeanObject,
    mut v_hl_1643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1644_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(
            v_k_1640_, v_v_1641_, v_t_1642_,
        );
    return v___x_1644_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___boxed(
    mut v_00_u03b2_1645_: *mut leanh::LeanObject,
    mut v_k_1646_: *mut leanh::LeanObject,
    mut v_v_1647_: *mut leanh::LeanObject,
    mut v_t_1648_: *mut leanh::LeanObject,
    mut v_hl_1649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_boxed_1650_: u64 = 0;
    let mut v_res_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_1650_ = leanh::lean_unbox_uint64(v_k_1646_);
    leanh::lean_dec_ref(v_k_1646_);
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
    mut v_mutex_1652_: *mut leanh::LeanObject,
    mut v_k_1653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1655_ = leanh::lean_ctor_get(v_mutex_1652_, 0);
    leanh::lean_inc(v_ref_1655_);
    v_mutex_1656_ = leanh::lean_ctor_get(v_mutex_1652_, 1);
    leanh::lean_inc(v_mutex_1656_);
    leanh::lean_dec_ref(v_mutex_1652_);
    v___x_1657_ = lean_io_basemutex_lock(v_mutex_1656_);
    v___x_1658_ = leanh::lean_apply_2(v_k_1653_, v_ref_1655_, leanh::lean_box(0));
    v___x_1659_ = lean_io_basemutex_unlock(v_mutex_1656_);
    leanh::lean_dec(v_mutex_1656_);
    return v___x_1658_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg___boxed(
    mut v_mutex_1660_: *mut leanh::LeanObject,
    mut v_k_1661_: *mut leanh::LeanObject,
    mut v___y_1662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1663_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(
        v_mutex_1660_,
        v_k_1661_,
    );
    return v_res_1663_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(
    mut v_00_u03b1_1664_: *mut leanh::LeanObject,
    mut v_00_u03b2_1665_: *mut leanh::LeanObject,
    mut v_mutex_1666_: *mut leanh::LeanObject,
    mut v_k_1667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1669_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(
        v_mutex_1666_,
        v_k_1667_,
    );
    return v___x_1669_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___boxed(
    mut v_00_u03b1_1670_: *mut leanh::LeanObject,
    mut v_00_u03b2_1671_: *mut leanh::LeanObject,
    mut v_mutex_1672_: *mut leanh::LeanObject,
    mut v_k_1673_: *mut leanh::LeanObject,
    mut v___y_1674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1675_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(
        v_00_u03b1_1670_,
        v_00_u03b2_1671_,
        v_mutex_1672_,
        v_k_1673_,
    );
    return v_res_1675_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(
    mut v_x_1676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_x_1676_);
    return v_x_1676_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0___boxed(
    mut v_x_1677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1678_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(v_x_1677_);
    leanh::lean_dec_ref(v_x_1677_);
    return v_res_1678_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(
    mut v___x_1679_: u64,
    mut v_x_1680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1681_ = leanh::lean_box_uint64(v___x_1679_);
    v___x_1682_ = lean_array_push(v_x_1680_, v___x_1681_);
    return v___x_1682_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed(
    mut v___x_1683_: *mut leanh::LeanObject,
    mut v_x_1684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1350__boxed_1685_: u64 = 0;
    let mut v_res_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1350__boxed_1685_ = leanh::lean_unbox_uint64(v___x_1683_);
    leanh::lean_dec_ref(v___x_1683_);
    v_res_1686_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(v___x_1350__boxed_1685_, v_x_1684_);
    return v_res_1686_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(
    mut v___x_1688_: u64,
    mut v_k_1689_: u64,
    mut v_t_1690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1698_: u8 = 0;
    let mut v___x_1699_: u64 = 0;
    let mut v___x_1700_: u8 = 0;
    let mut v___x_1701_: u64 = 0;
    let mut v___x_1702_: u8 = 0;
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1690_) == 0 {
                    v_size_1691_ = leanh::lean_ctor_get(v_t_1690_, 0);
                    v_k_1692_ = leanh::lean_ctor_get(v_t_1690_, 1);
                    v_v_1693_ = leanh::lean_ctor_get(v_t_1690_, 2);
                    v_l_1694_ = leanh::lean_ctor_get(v_t_1690_, 3);
                    v_r_1695_ = leanh::lean_ctor_get(v_t_1690_, 4);
                    v_isSharedCheck_1719_ = (!leanh::lean_is_exclusive(v_t_1690_)) as u8;
                    if v_isSharedCheck_1719_ == 0 {
                        v___x_1697_ = v_t_1690_;
                        v_isShared_1698_ = v_isSharedCheck_1719_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_1695_);
                        leanh::lean_inc(v_l_1694_);
                        leanh::lean_inc(v_v_1693_);
                        leanh::lean_inc(v_k_1692_);
                        leanh::lean_inc(v_size_1691_);
                        leanh::lean_dec(v_t_1690_);
                        v___x_1697_ = leanh::lean_box(0);
                        v_isShared_1698_ = v_isSharedCheck_1719_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_t_1690_;
                }
            }
            1 => {
                v___x_1699_ = leanh::lean_unbox_uint64(v_k_1692_);
                v___x_1700_ = lean_uint64_dec_lt(v_k_1689_, v___x_1699_);
                if v___x_1700_ == 0 {
                    v___x_1701_ = leanh::lean_unbox_uint64(v_k_1692_);
                    v___x_1702_ = lean_uint64_dec_eq(v_k_1689_, v___x_1701_);
                    if v___x_1702_ == 0 {
                        v___x_1703_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v___x_1688_, v_k_1689_, v_r_1695_);
                        if v_isShared_1698_ == 0 {
                            leanh::lean_ctor_set(v___x_1697_, 4, v___x_1703_);
                            v___x_1705_ = v___x_1697_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1706_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_size_1691_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_k_1692_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_v_1693_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 3, v_l_1694_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 4, v___x_1703_);
                            v___x_1705_ = v_reuseFailAlloc_1706_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_k_1692_);
                        v___f_1707_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0;
                        v___x_1708_ = leanh::lean_box_uint64(v___x_1688_);
                        v___f_1709_ = leanh::lean_alloc_closure(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                        leanh::lean_closure_set(v___f_1709_, 0, v___x_1708_);
                        v___x_1710_ = l_Prod_map___redArg(v___f_1707_, v___f_1709_, v_v_1693_);
                        v___x_1711_ = leanh::lean_box_uint64(v_k_1689_);
                        if v_isShared_1698_ == 0 {
                            leanh::lean_ctor_set(v___x_1697_, 2, v___x_1710_);
                            leanh::lean_ctor_set(v___x_1697_, 1, v___x_1711_);
                            v___x_1713_ = v___x_1697_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1714_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_size_1691_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 1, v___x_1711_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 2, v___x_1710_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 3, v_l_1694_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 4, v_r_1695_);
                            v___x_1713_ = v_reuseFailAlloc_1714_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_1715_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v___x_1688_, v_k_1689_, v_l_1694_);
                    if v_isShared_1698_ == 0 {
                        leanh::lean_ctor_set(v___x_1697_, 3, v___x_1715_);
                        v___x_1717_ = v___x_1697_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1718_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_size_1691_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_k_1692_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 2, v_v_1693_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 3, v___x_1715_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 4, v_r_1695_);
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
    mut v___x_1720_: *mut leanh::LeanObject,
    mut v_k_1721_: *mut leanh::LeanObject,
    mut v_t_1722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1362__boxed_1723_: u64 = 0;
    let mut v_k_boxed_1724_: u64 = 0;
    let mut v_res_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1362__boxed_1723_ = leanh::lean_unbox_uint64(v___x_1720_);
    leanh::lean_dec_ref(v___x_1720_);
    v_k_boxed_1724_ = leanh::lean_unbox_uint64(v_k_1721_);
    leanh::lean_dec_ref(v_k_1721_);
    v_res_1725_ =
        l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(
            v___x_1362__boxed_1723_,
            v_k_boxed_1724_,
            v_t_1722_,
        );
    return v_res_1725_;
}
pub unsafe fn l_Std_CancellationContext_fork___lam__0(
    mut v_token_1726_: *mut leanh::LeanObject,
    mut v_id_1727_: u64,
    mut v_state_1728_: *mut leanh::LeanObject,
    mut v_root_1729_: *mut leanh::LeanObject,
    mut v___y_1730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1732_: u8 = 0;
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tokens_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1736_: u64 = 0;
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: u64 = 0;
    let mut v___x_1745_: u64 = 0;
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1732_ = l_Std_CancellationToken_isCancelled(v_token_1726_);
                if v___x_1732_ == 0 {
                    v___x_1733_ = l_Std_CancellationToken_new();
                    v___x_1734_ = lean_st_ref_get(v___y_1730_);
                    v_tokens_1735_ = leanh::lean_ctor_get(v___x_1734_, 0);
                    v_id_1736_ = leanh::lean_ctor_get_uint64(
                        v___x_1734_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_isSharedCheck_1751_ = (!leanh::lean_is_exclusive(v___x_1734_)) as u8;
                    if v_isSharedCheck_1751_ == 0 {
                        v___x_1738_ = v___x_1734_;
                        v_isShared_1739_ = v_isSharedCheck_1751_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tokens_1735_);
                        leanh::lean_dec(v___x_1734_);
                        v___x_1738_ = leanh::lean_box(0);
                        v_isShared_1739_ = v_isSharedCheck_1751_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_state_1728_);
                    leanh::lean_inc_ref(v_root_1729_);
                    return v_root_1729_;
                }
            }
            1 => {
                v___x_1740_ = l_Std_CancellationContext_new___closed__0;
                leanh::lean_inc_ref(v___x_1733_);
                v___x_1741_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1741_, 0, v___x_1733_);
                leanh::lean_ctor_set(v___x_1741_, 1, v___x_1740_);
                v___x_1742_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_id_1736_, v___x_1741_, v_tokens_1735_);
                v___x_1743_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v_id_1736_, v_id_1727_, v___x_1742_);
                v___x_1744_ = 1u64;
                v___x_1745_ = lean_uint64_add(v_id_1736_, v___x_1744_);
                if v_isShared_1739_ == 0 {
                    leanh::lean_ctor_set(v___x_1738_, 0, v___x_1743_);
                    v___x_1747_ = v___x_1738_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1750_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1743_);
                    v___x_1747_ = v_reuseFailAlloc_1750_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint64(
                    v___x_1747_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1745_,
                );
                v___x_1748_ = lean_st_ref_set(v___y_1730_, v___x_1747_);
                v___x_1749_ = leanh::lean_alloc_ctor(0, 2, (8) as u32);
                leanh::lean_ctor_set(v___x_1749_, 0, v_state_1728_);
                leanh::lean_ctor_set(v___x_1749_, 1, v___x_1733_);
                leanh::lean_ctor_set_uint64(
                    v___x_1749_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v_id_1736_,
                );
                return v___x_1749_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CancellationContext_fork___lam__0___boxed(
    mut v_token_1752_: *mut leanh::LeanObject,
    mut v_id_1753_: *mut leanh::LeanObject,
    mut v_state_1754_: *mut leanh::LeanObject,
    mut v_root_1755_: *mut leanh::LeanObject,
    mut v___y_1756_: *mut leanh::LeanObject,
    mut v___y_1757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_boxed_1758_: u64 = 0;
    let mut v_res_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_id_boxed_1758_ = leanh::lean_unbox_uint64(v_id_1753_);
    leanh::lean_dec_ref(v_id_1753_);
    v_res_1759_ = l_Std_CancellationContext_fork___lam__0(
        v_token_1752_,
        v_id_boxed_1758_,
        v_state_1754_,
        v_root_1755_,
        v___y_1756_,
    );
    leanh::lean_dec(v___y_1756_);
    leanh::lean_dec_ref(v_root_1755_);
    return v_res_1759_;
}
pub unsafe fn l_Std_CancellationContext_fork(
    mut v_root_1760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_state_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_token_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1764_: u64 = 0;
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_state_1762_ = leanh::lean_ctor_get(v_root_1760_, 0);
    leanh::lean_inc_ref_n(v_state_1762_, 2);
    v_token_1763_ = leanh::lean_ctor_get(v_root_1760_, 1);
    leanh::lean_inc_ref(v_token_1763_);
    v_id_1764_ = leanh::lean_ctor_get_uint64(
        v_root_1760_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    v___x_1765_ = leanh::lean_box_uint64(v_id_1764_);
    v___f_1766_ = leanh::lean_alloc_closure(
        l_Std_CancellationContext_fork___lam__0___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    leanh::lean_closure_set(v___f_1766_, 0, v_token_1763_);
    leanh::lean_closure_set(v___f_1766_, 1, v___x_1765_);
    leanh::lean_closure_set(v___f_1766_, 2, v_state_1762_);
    leanh::lean_closure_set(v___f_1766_, 3, v_root_1760_);
    v___x_1767_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(
        v_state_1762_,
        v___f_1766_,
    );
    return v___x_1767_;
}
pub unsafe fn l_Std_CancellationContext_fork___boxed(
    mut v_root_1768_: *mut leanh::LeanObject,
    mut v_a_1769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1770_ = l_Std_CancellationContext_fork(v_root_1768_);
    return v_res_1770_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(
    mut v_k_1771_: u64,
    mut v_t_1772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1779_: u8 = 0;
    let mut v___x_1780_: u64 = 0;
    let mut v___x_1781_: u8 = 0;
    let mut v___x_1782_: u64 = 0;
    let mut v___x_1783_: u8 = 0;
    let mut v_impl_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: u8 = 0;
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1802_: u8 = 0;
    let mut v_size_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1814_: u8 = 0;
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1840_: u8 = 0;
    let mut v_unused_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1854_: u8 = 0;
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut v_unused_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1865_: u8 = 0;
    let mut v_unused_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1883_: u8 = 0;
    let mut v_size_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1893_: u8 = 0;
    let mut v_unused_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1900_: u8 = 0;
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1908_: u8 = 0;
    let mut v_unused_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v_k_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1933_: u8 = 0;
    let mut v_unused_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1937_: u8 = 0;
    let mut v_unused_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1962_: u8 = 0;
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: u8 = 0;
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v_size_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: u8 = 0;
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1990_: u8 = 0;
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2015_: u8 = 0;
    let mut v_unused_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2030_: u8 = 0;
    let mut v_unused_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v_k_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2056_: u8 = 0;
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2067_: u8 = 0;
    let mut v_unused_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2089_: u8 = 0;
    let mut v_unused_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2095_: u8 = 0;
    let mut v_unused_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2103_: u8 = 0;
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: u8 = 0;
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2119_: u8 = 0;
    let mut v_size_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: u8 = 0;
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2131_: u8 = 0;
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2143_: u8 = 0;
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2147_: u8 = 0;
    let mut v_unused_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2166_: u8 = 0;
    let mut v_unused_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2182_: u8 = 0;
    let mut v_unused_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2190_: u8 = 0;
    let mut v_k_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2211_: u8 = 0;
    let mut v_unused_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2219_: u8 = 0;
    let mut v_k_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2226_: u8 = 0;
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut v_unused_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut v_unused_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2253_: u8 = 0;
    let mut v_unused_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: u8 = 0;
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2277_: u8 = 0;
    let mut v_size_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: u8 = 0;
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2289_: u8 = 0;
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2314_: u8 = 0;
    let mut v_unused_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2327_: u8 = 0;
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2331_: u8 = 0;
    let mut v_unused_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2338_: u8 = 0;
    let mut v_unused_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v_size_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2366_: u8 = 0;
    let mut v_unused_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2373_: u8 = 0;
    let mut v_k_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2378_: u8 = 0;
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2389_: u8 = 0;
    let mut v_unused_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2393_: u8 = 0;
    let mut v_unused_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2402_: u8 = 0;
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2410_: u8 = 0;
    let mut v_unused_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2419_: u8 = 0;
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut v_unused_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2433_: u8 = 0;
    let mut v_unused_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1772_) == 0 {
                    v_k_1773_ = leanh::lean_ctor_get(v_t_1772_, 1);
                    v_v_1774_ = leanh::lean_ctor_get(v_t_1772_, 2);
                    v_l_1775_ = leanh::lean_ctor_get(v_t_1772_, 3);
                    v_r_1776_ = leanh::lean_ctor_get(v_t_1772_, 4);
                    v_isSharedCheck_2433_ = (!leanh::lean_is_exclusive(v_t_1772_)) as u8;
                    if v_isSharedCheck_2433_ == 0 {
                        v_unused_2434_ = leanh::lean_ctor_get(v_t_1772_, 0);
                        leanh::lean_dec(v_unused_2434_);
                        v___x_1778_ = v_t_1772_;
                        v_isShared_1779_ = v_isSharedCheck_2433_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_1776_);
                        leanh::lean_inc(v_l_1775_);
                        leanh::lean_inc(v_v_1774_);
                        leanh::lean_inc(v_k_1773_);
                        leanh::lean_dec(v_t_1772_);
                        v___x_1778_ = leanh::lean_box(0);
                        v_isShared_1779_ = v_isSharedCheck_2433_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_t_1772_;
                }
            }
            1 => {
                v___x_1780_ = leanh::lean_unbox_uint64(v_k_1773_);
                v___x_1781_ = lean_uint64_dec_lt(v_k_1771_, v___x_1780_);
                if v___x_1781_ == 0 {
                    v___x_1782_ = leanh::lean_unbox_uint64(v_k_1773_);
                    v___x_1783_ = lean_uint64_dec_eq(v_k_1771_, v___x_1782_);
                    if v___x_1783_ == 0 {
                        v_impl_1784_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_1771_, v_r_1776_);
                        v___x_1785_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_impl_1784_) == 0 {
                            if leanh::lean_obj_tag(v_l_1775_) == 0 {
                                v_size_1786_ = leanh::lean_ctor_get(v_impl_1784_, 0);
                                leanh::lean_inc(v_size_1786_);
                                v_size_1787_ = leanh::lean_ctor_get(v_l_1775_, 0);
                                v_k_1788_ = leanh::lean_ctor_get(v_l_1775_, 1);
                                v_v_1789_ = leanh::lean_ctor_get(v_l_1775_, 2);
                                v_l_1790_ = leanh::lean_ctor_get(v_l_1775_, 3);
                                v_r_1791_ = leanh::lean_ctor_get(v_l_1775_, 4);
                                leanh::lean_inc(v_r_1791_);
                                v___x_1792_ = leanh::lean_unsigned_to_nat(3);
                                v___x_1793_ = lean_nat_mul(v___x_1792_, v_size_1786_);
                                v___x_1794_ = lean_nat_dec_lt(v___x_1793_, v_size_1787_);
                                leanh::lean_dec(v___x_1793_);
                                if v___x_1794_ == 0 {
                                    leanh::lean_dec(v_r_1791_);
                                    v___x_1795_ = lean_nat_add(v___x_1785_, v_size_1787_);
                                    v___x_1796_ = lean_nat_add(v___x_1795_, v_size_1786_);
                                    leanh::lean_dec(v_size_1786_);
                                    leanh::lean_dec(v___x_1795_);
                                    if v_isShared_1779_ == 0 {
                                        leanh::lean_ctor_set(v___x_1778_, 4, v_impl_1784_);
                                        leanh::lean_ctor_set(v___x_1778_, 0, v___x_1796_);
                                        v___x_1798_ = v___x_1778_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1799_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1799_,
                                            0,
                                            v___x_1796_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1799_,
                                            1,
                                            v_k_1773_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1799_,
                                            2,
                                            v_v_1774_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1799_,
                                            3,
                                            v_l_1775_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1799_,
                                            4,
                                            v_impl_1784_,
                                        );
                                        v___x_1798_ = v_reuseFailAlloc_1799_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_l_1790_);
                                    leanh::lean_inc(v_v_1789_);
                                    leanh::lean_inc(v_k_1788_);
                                    leanh::lean_inc(v_size_1787_);
                                    v_isSharedCheck_1865_ =
                                        (!leanh::lean_is_exclusive(v_l_1775_)) as u8;
                                    if v_isSharedCheck_1865_ == 0 {
                                        v_unused_1866_ = leanh::lean_ctor_get(v_l_1775_, 4);
                                        leanh::lean_dec(v_unused_1866_);
                                        v_unused_1867_ = leanh::lean_ctor_get(v_l_1775_, 3);
                                        leanh::lean_dec(v_unused_1867_);
                                        v_unused_1868_ = leanh::lean_ctor_get(v_l_1775_, 2);
                                        leanh::lean_dec(v_unused_1868_);
                                        v_unused_1869_ = leanh::lean_ctor_get(v_l_1775_, 1);
                                        leanh::lean_dec(v_unused_1869_);
                                        v_unused_1870_ = leanh::lean_ctor_get(v_l_1775_, 0);
                                        leanh::lean_dec(v_unused_1870_);
                                        v___x_1801_ = v_l_1775_;
                                        v_isShared_1802_ = v_isSharedCheck_1865_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_l_1775_);
                                        v___x_1801_ = leanh::lean_box(0);
                                        v_isShared_1802_ = v_isSharedCheck_1865_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_1871_ = leanh::lean_ctor_get(v_impl_1784_, 0);
                                leanh::lean_inc(v_size_1871_);
                                v___x_1872_ = lean_nat_add(v___x_1785_, v_size_1871_);
                                leanh::lean_dec(v_size_1871_);
                                if v_isShared_1779_ == 0 {
                                    leanh::lean_ctor_set(v___x_1778_, 4, v_impl_1784_);
                                    leanh::lean_ctor_set(v___x_1778_, 0, v___x_1872_);
                                    v___x_1874_ = v___x_1778_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1875_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1875_,
                                        0,
                                        v___x_1872_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1875_,
                                        1,
                                        v_k_1773_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1875_,
                                        2,
                                        v_v_1774_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1875_,
                                        3,
                                        v_l_1775_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1875_,
                                        4,
                                        v_impl_1784_,
                                    );
                                    v___x_1874_ = v_reuseFailAlloc_1875_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v_l_1775_) == 0 {
                                v_l_1876_ = leanh::lean_ctor_get(v_l_1775_, 3);
                                if leanh::lean_obj_tag(v_l_1876_) == 0 {
                                    leanh::lean_inc_ref(v_l_1876_);
                                    v_r_1877_ = leanh::lean_ctor_get(v_l_1775_, 4);
                                    leanh::lean_inc(v_r_1877_);
                                    if leanh::lean_obj_tag(v_r_1877_) == 0 {
                                        v_size_1878_ = leanh::lean_ctor_get(v_l_1775_, 0);
                                        v_k_1879_ = leanh::lean_ctor_get(v_l_1775_, 1);
                                        v_v_1880_ = leanh::lean_ctor_get(v_l_1775_, 2);
                                        v_isSharedCheck_1893_ =
                                            (!leanh::lean_is_exclusive(v_l_1775_)) as u8;
                                        if v_isSharedCheck_1893_ == 0 {
                                            v_unused_1894_ =
                                                leanh::lean_ctor_get(v_l_1775_, 4);
                                            leanh::lean_dec(v_unused_1894_);
                                            v_unused_1895_ =
                                                leanh::lean_ctor_get(v_l_1775_, 3);
                                            leanh::lean_dec(v_unused_1895_);
                                            v___x_1882_ = v_l_1775_;
                                            v_isShared_1883_ = v_isSharedCheck_1893_;
                                            state = 14;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1880_);
                                            leanh::lean_inc(v_k_1879_);
                                            leanh::lean_inc(v_size_1878_);
                                            leanh::lean_dec(v_l_1775_);
                                            v___x_1882_ = leanh::lean_box(0);
                                            v_isShared_1883_ = v_isSharedCheck_1893_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_1896_ = leanh::lean_ctor_get(v_l_1775_, 1);
                                        v_v_1897_ = leanh::lean_ctor_get(v_l_1775_, 2);
                                        v_isSharedCheck_1908_ =
                                            (!leanh::lean_is_exclusive(v_l_1775_)) as u8;
                                        if v_isSharedCheck_1908_ == 0 {
                                            v_unused_1909_ =
                                                leanh::lean_ctor_get(v_l_1775_, 4);
                                            leanh::lean_dec(v_unused_1909_);
                                            v_unused_1910_ =
                                                leanh::lean_ctor_get(v_l_1775_, 3);
                                            leanh::lean_dec(v_unused_1910_);
                                            v_unused_1911_ =
                                                leanh::lean_ctor_get(v_l_1775_, 0);
                                            leanh::lean_dec(v_unused_1911_);
                                            v___x_1899_ = v_l_1775_;
                                            v_isShared_1900_ = v_isSharedCheck_1908_;
                                            state = 17;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1897_);
                                            leanh::lean_inc(v_k_1896_);
                                            leanh::lean_dec(v_l_1775_);
                                            v___x_1899_ = leanh::lean_box(0);
                                            v_isShared_1900_ = v_isSharedCheck_1908_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_1912_ = leanh::lean_ctor_get(v_l_1775_, 4);
                                    leanh::lean_inc(v_r_1912_);
                                    if leanh::lean_obj_tag(v_r_1912_) == 0 {
                                        leanh::lean_inc(v_l_1876_);
                                        v_k_1913_ = leanh::lean_ctor_get(v_l_1775_, 1);
                                        v_v_1914_ = leanh::lean_ctor_get(v_l_1775_, 2);
                                        v_isSharedCheck_1937_ =
                                            (!leanh::lean_is_exclusive(v_l_1775_)) as u8;
                                        if v_isSharedCheck_1937_ == 0 {
                                            v_unused_1938_ =
                                                leanh::lean_ctor_get(v_l_1775_, 4);
                                            leanh::lean_dec(v_unused_1938_);
                                            v_unused_1939_ =
                                                leanh::lean_ctor_get(v_l_1775_, 3);
                                            leanh::lean_dec(v_unused_1939_);
                                            v_unused_1940_ =
                                                leanh::lean_ctor_get(v_l_1775_, 0);
                                            leanh::lean_dec(v_unused_1940_);
                                            v___x_1916_ = v_l_1775_;
                                            v_isShared_1917_ = v_isSharedCheck_1937_;
                                            state = 20;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1914_);
                                            leanh::lean_inc(v_k_1913_);
                                            leanh::lean_dec(v_l_1775_);
                                            v___x_1916_ = leanh::lean_box(0);
                                            v_isShared_1917_ = v_isSharedCheck_1937_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_1941_ = leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_1779_ == 0 {
                                            leanh::lean_ctor_set(v___x_1778_, 4, v_r_1912_);
                                            leanh::lean_ctor_set(
                                                v___x_1778_,
                                                0,
                                                v___x_1941_,
                                            );
                                            v___x_1943_ = v___x_1778_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_1944_ =
                                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1944_,
                                                0,
                                                v___x_1941_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1944_,
                                                1,
                                                v_k_1773_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1944_,
                                                2,
                                                v_v_1774_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1944_,
                                                3,
                                                v_l_1775_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1944_,
                                                4,
                                                v_r_1912_,
                                            );
                                            v___x_1943_ = v_reuseFailAlloc_1944_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_1779_ == 0 {
                                    leanh::lean_ctor_set(v___x_1778_, 4, v_l_1775_);
                                    leanh::lean_ctor_set(v___x_1778_, 0, v___x_1785_);
                                    v___x_1946_ = v___x_1778_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1947_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1947_,
                                        0,
                                        v___x_1785_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1947_,
                                        1,
                                        v_k_1773_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1947_,
                                        2,
                                        v_v_1774_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1947_,
                                        3,
                                        v_l_1775_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1947_,
                                        4,
                                        v_l_1775_,
                                    );
                                    v___x_1946_ = v_reuseFailAlloc_1947_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_1778_);
                        leanh::lean_dec(v_v_1774_);
                        leanh::lean_dec(v_k_1773_);
                        if leanh::lean_obj_tag(v_l_1775_) == 0 {
                            if leanh::lean_obj_tag(v_r_1776_) == 0 {
                                v_size_1948_ = leanh::lean_ctor_get(v_l_1775_, 0);
                                v_k_1949_ = leanh::lean_ctor_get(v_l_1775_, 1);
                                v_v_1950_ = leanh::lean_ctor_get(v_l_1775_, 2);
                                v_l_1951_ = leanh::lean_ctor_get(v_l_1775_, 3);
                                v_r_1952_ = leanh::lean_ctor_get(v_l_1775_, 4);
                                leanh::lean_inc(v_r_1952_);
                                v_size_1953_ = leanh::lean_ctor_get(v_r_1776_, 0);
                                v_k_1954_ = leanh::lean_ctor_get(v_r_1776_, 1);
                                v_v_1955_ = leanh::lean_ctor_get(v_r_1776_, 2);
                                v_l_1956_ = leanh::lean_ctor_get(v_r_1776_, 3);
                                leanh::lean_inc(v_l_1956_);
                                v_r_1957_ = leanh::lean_ctor_get(v_r_1776_, 4);
                                v___x_1958_ = leanh::lean_unsigned_to_nat(1);
                                v___x_1959_ = lean_nat_dec_lt(v_size_1948_, v_size_1953_);
                                if v___x_1959_ == 0 {
                                    leanh::lean_inc(v_l_1951_);
                                    leanh::lean_inc(v_v_1950_);
                                    leanh::lean_inc(v_k_1949_);
                                    v_isSharedCheck_2095_ =
                                        (!leanh::lean_is_exclusive(v_l_1775_)) as u8;
                                    if v_isSharedCheck_2095_ == 0 {
                                        v_unused_2096_ = leanh::lean_ctor_get(v_l_1775_, 4);
                                        leanh::lean_dec(v_unused_2096_);
                                        v_unused_2097_ = leanh::lean_ctor_get(v_l_1775_, 3);
                                        leanh::lean_dec(v_unused_2097_);
                                        v_unused_2098_ = leanh::lean_ctor_get(v_l_1775_, 2);
                                        leanh::lean_dec(v_unused_2098_);
                                        v_unused_2099_ = leanh::lean_ctor_get(v_l_1775_, 1);
                                        leanh::lean_dec(v_unused_2099_);
                                        v_unused_2100_ = leanh::lean_ctor_get(v_l_1775_, 0);
                                        leanh::lean_dec(v_unused_2100_);
                                        v___x_1961_ = v_l_1775_;
                                        v_isShared_1962_ = v_isSharedCheck_2095_;
                                        state = 27;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_l_1775_);
                                        v___x_1961_ = leanh::lean_box(0);
                                        v_isShared_1962_ = v_isSharedCheck_2095_;
                                        state = 27;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_r_1957_);
                                    leanh::lean_inc(v_v_1955_);
                                    leanh::lean_inc(v_k_1954_);
                                    v_isSharedCheck_2253_ =
                                        (!leanh::lean_is_exclusive(v_r_1776_)) as u8;
                                    if v_isSharedCheck_2253_ == 0 {
                                        v_unused_2254_ = leanh::lean_ctor_get(v_r_1776_, 4);
                                        leanh::lean_dec(v_unused_2254_);
                                        v_unused_2255_ = leanh::lean_ctor_get(v_r_1776_, 3);
                                        leanh::lean_dec(v_unused_2255_);
                                        v_unused_2256_ = leanh::lean_ctor_get(v_r_1776_, 2);
                                        leanh::lean_dec(v_unused_2256_);
                                        v_unused_2257_ = leanh::lean_ctor_get(v_r_1776_, 1);
                                        leanh::lean_dec(v_unused_2257_);
                                        v_unused_2258_ = leanh::lean_ctor_get(v_r_1776_, 0);
                                        leanh::lean_dec(v_unused_2258_);
                                        v___x_2102_ = v_r_1776_;
                                        v_isShared_2103_ = v_isSharedCheck_2253_;
                                        state = 49;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_r_1776_);
                                        v___x_2102_ = leanh::lean_box(0);
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
                    v___x_2260_ = leanh::lean_unsigned_to_nat(1);
                    if leanh::lean_obj_tag(v_impl_2259_) == 0 {
                        if leanh::lean_obj_tag(v_r_1776_) == 0 {
                            v_size_2261_ = leanh::lean_ctor_get(v_impl_2259_, 0);
                            leanh::lean_inc(v_size_2261_);
                            v_size_2262_ = leanh::lean_ctor_get(v_r_1776_, 0);
                            v_k_2263_ = leanh::lean_ctor_get(v_r_1776_, 1);
                            v_v_2264_ = leanh::lean_ctor_get(v_r_1776_, 2);
                            v_l_2265_ = leanh::lean_ctor_get(v_r_1776_, 3);
                            leanh::lean_inc(v_l_2265_);
                            v_r_2266_ = leanh::lean_ctor_get(v_r_1776_, 4);
                            v___x_2267_ = leanh::lean_unsigned_to_nat(3);
                            v___x_2268_ = lean_nat_mul(v___x_2267_, v_size_2261_);
                            v___x_2269_ = lean_nat_dec_lt(v___x_2268_, v_size_2262_);
                            leanh::lean_dec(v___x_2268_);
                            if v___x_2269_ == 0 {
                                leanh::lean_dec(v_l_2265_);
                                v___x_2270_ = lean_nat_add(v___x_2260_, v_size_2261_);
                                leanh::lean_dec(v_size_2261_);
                                v___x_2271_ = lean_nat_add(v___x_2270_, v_size_2262_);
                                leanh::lean_dec(v___x_2270_);
                                if v_isShared_1779_ == 0 {
                                    leanh::lean_ctor_set(v___x_1778_, 3, v_impl_2259_);
                                    leanh::lean_ctor_set(v___x_1778_, 0, v___x_2271_);
                                    v___x_2273_ = v___x_1778_;
                                    state = 72;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2274_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2274_,
                                        0,
                                        v___x_2271_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2274_,
                                        1,
                                        v_k_1773_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2274_,
                                        2,
                                        v_v_1774_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2274_,
                                        3,
                                        v_impl_2259_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2274_,
                                        4,
                                        v_r_1776_,
                                    );
                                    v___x_2273_ = v_reuseFailAlloc_2274_;
                                    state = 72;
                                    continue;
                                }
                            } else {
                                leanh::lean_inc(v_r_2266_);
                                leanh::lean_inc(v_v_2264_);
                                leanh::lean_inc(v_k_2263_);
                                leanh::lean_inc(v_size_2262_);
                                v_isSharedCheck_2338_ =
                                    (!leanh::lean_is_exclusive(v_r_1776_)) as u8;
                                if v_isSharedCheck_2338_ == 0 {
                                    v_unused_2339_ = leanh::lean_ctor_get(v_r_1776_, 4);
                                    leanh::lean_dec(v_unused_2339_);
                                    v_unused_2340_ = leanh::lean_ctor_get(v_r_1776_, 3);
                                    leanh::lean_dec(v_unused_2340_);
                                    v_unused_2341_ = leanh::lean_ctor_get(v_r_1776_, 2);
                                    leanh::lean_dec(v_unused_2341_);
                                    v_unused_2342_ = leanh::lean_ctor_get(v_r_1776_, 1);
                                    leanh::lean_dec(v_unused_2342_);
                                    v_unused_2343_ = leanh::lean_ctor_get(v_r_1776_, 0);
                                    leanh::lean_dec(v_unused_2343_);
                                    v___x_2276_ = v_r_1776_;
                                    v_isShared_2277_ = v_isSharedCheck_2338_;
                                    state = 73;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_r_1776_);
                                    v___x_2276_ = leanh::lean_box(0);
                                    v_isShared_2277_ = v_isSharedCheck_2338_;
                                    state = 73;
                                    continue;
                                }
                            }
                        } else {
                            v_size_2344_ = leanh::lean_ctor_get(v_impl_2259_, 0);
                            leanh::lean_inc(v_size_2344_);
                            v___x_2345_ = lean_nat_add(v___x_2260_, v_size_2344_);
                            leanh::lean_dec(v_size_2344_);
                            if v_isShared_1779_ == 0 {
                                leanh::lean_ctor_set(v___x_1778_, 3, v_impl_2259_);
                                leanh::lean_ctor_set(v___x_1778_, 0, v___x_2345_);
                                v___x_2347_ = v___x_1778_;
                                state = 83;
                                continue;
                            } else {
                                v_reuseFailAlloc_2348_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_k_1773_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 2, v_v_1774_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2348_,
                                    3,
                                    v_impl_2259_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 4, v_r_1776_);
                                v___x_2347_ = v_reuseFailAlloc_2348_;
                                state = 83;
                                continue;
                            }
                        }
                    } else {
                        if leanh::lean_obj_tag(v_r_1776_) == 0 {
                            v_l_2349_ = leanh::lean_ctor_get(v_r_1776_, 3);
                            leanh::lean_inc(v_l_2349_);
                            if leanh::lean_obj_tag(v_l_2349_) == 0 {
                                v_r_2350_ = leanh::lean_ctor_get(v_r_1776_, 4);
                                leanh::lean_inc(v_r_2350_);
                                if leanh::lean_obj_tag(v_r_2350_) == 0 {
                                    v_size_2351_ = leanh::lean_ctor_get(v_r_1776_, 0);
                                    v_k_2352_ = leanh::lean_ctor_get(v_r_1776_, 1);
                                    v_v_2353_ = leanh::lean_ctor_get(v_r_1776_, 2);
                                    v_isSharedCheck_2366_ =
                                        (!leanh::lean_is_exclusive(v_r_1776_)) as u8;
                                    if v_isSharedCheck_2366_ == 0 {
                                        v_unused_2367_ = leanh::lean_ctor_get(v_r_1776_, 4);
                                        leanh::lean_dec(v_unused_2367_);
                                        v_unused_2368_ = leanh::lean_ctor_get(v_r_1776_, 3);
                                        leanh::lean_dec(v_unused_2368_);
                                        v___x_2355_ = v_r_1776_;
                                        v_isShared_2356_ = v_isSharedCheck_2366_;
                                        state = 84;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_2353_);
                                        leanh::lean_inc(v_k_2352_);
                                        leanh::lean_inc(v_size_2351_);
                                        leanh::lean_dec(v_r_1776_);
                                        v___x_2355_ = leanh::lean_box(0);
                                        v_isShared_2356_ = v_isSharedCheck_2366_;
                                        state = 84;
                                        continue;
                                    }
                                } else {
                                    v_k_2369_ = leanh::lean_ctor_get(v_r_1776_, 1);
                                    v_v_2370_ = leanh::lean_ctor_get(v_r_1776_, 2);
                                    v_isSharedCheck_2393_ =
                                        (!leanh::lean_is_exclusive(v_r_1776_)) as u8;
                                    if v_isSharedCheck_2393_ == 0 {
                                        v_unused_2394_ = leanh::lean_ctor_get(v_r_1776_, 4);
                                        leanh::lean_dec(v_unused_2394_);
                                        v_unused_2395_ = leanh::lean_ctor_get(v_r_1776_, 3);
                                        leanh::lean_dec(v_unused_2395_);
                                        v_unused_2396_ = leanh::lean_ctor_get(v_r_1776_, 0);
                                        leanh::lean_dec(v_unused_2396_);
                                        v___x_2372_ = v_r_1776_;
                                        v_isShared_2373_ = v_isSharedCheck_2393_;
                                        state = 87;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_2370_);
                                        leanh::lean_inc(v_k_2369_);
                                        leanh::lean_dec(v_r_1776_);
                                        v___x_2372_ = leanh::lean_box(0);
                                        v_isShared_2373_ = v_isSharedCheck_2393_;
                                        state = 87;
                                        continue;
                                    }
                                }
                            } else {
                                v_r_2397_ = leanh::lean_ctor_get(v_r_1776_, 4);
                                leanh::lean_inc(v_r_2397_);
                                if leanh::lean_obj_tag(v_r_2397_) == 0 {
                                    v_k_2398_ = leanh::lean_ctor_get(v_r_1776_, 1);
                                    v_v_2399_ = leanh::lean_ctor_get(v_r_1776_, 2);
                                    v_isSharedCheck_2410_ =
                                        (!leanh::lean_is_exclusive(v_r_1776_)) as u8;
                                    if v_isSharedCheck_2410_ == 0 {
                                        v_unused_2411_ = leanh::lean_ctor_get(v_r_1776_, 4);
                                        leanh::lean_dec(v_unused_2411_);
                                        v_unused_2412_ = leanh::lean_ctor_get(v_r_1776_, 3);
                                        leanh::lean_dec(v_unused_2412_);
                                        v_unused_2413_ = leanh::lean_ctor_get(v_r_1776_, 0);
                                        leanh::lean_dec(v_unused_2413_);
                                        v___x_2401_ = v_r_1776_;
                                        v_isShared_2402_ = v_isSharedCheck_2410_;
                                        state = 92;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_2399_);
                                        leanh::lean_inc(v_k_2398_);
                                        leanh::lean_dec(v_r_1776_);
                                        v___x_2401_ = leanh::lean_box(0);
                                        v_isShared_2402_ = v_isSharedCheck_2410_;
                                        state = 92;
                                        continue;
                                    }
                                } else {
                                    v_size_2414_ = leanh::lean_ctor_get(v_r_1776_, 0);
                                    v_k_2415_ = leanh::lean_ctor_get(v_r_1776_, 1);
                                    v_v_2416_ = leanh::lean_ctor_get(v_r_1776_, 2);
                                    v_isSharedCheck_2427_ =
                                        (!leanh::lean_is_exclusive(v_r_1776_)) as u8;
                                    if v_isSharedCheck_2427_ == 0 {
                                        v_unused_2428_ = leanh::lean_ctor_get(v_r_1776_, 4);
                                        leanh::lean_dec(v_unused_2428_);
                                        v_unused_2429_ = leanh::lean_ctor_get(v_r_1776_, 3);
                                        leanh::lean_dec(v_unused_2429_);
                                        v___x_2418_ = v_r_1776_;
                                        v_isShared_2419_ = v_isSharedCheck_2427_;
                                        state = 95;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_2416_);
                                        leanh::lean_inc(v_k_2415_);
                                        leanh::lean_inc(v_size_2414_);
                                        leanh::lean_dec(v_r_1776_);
                                        v___x_2418_ = leanh::lean_box(0);
                                        v_isShared_2419_ = v_isSharedCheck_2427_;
                                        state = 95;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            if v_isShared_1779_ == 0 {
                                leanh::lean_ctor_set(v___x_1778_, 3, v_r_1776_);
                                leanh::lean_ctor_set(v___x_1778_, 0, v___x_2260_);
                                v___x_2431_ = v___x_1778_;
                                state = 98;
                                continue;
                            } else {
                                v_reuseFailAlloc_2432_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2260_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_k_1773_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 2, v_v_1774_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 3, v_r_1776_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 4, v_r_1776_);
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
                v_size_1803_ = leanh::lean_ctor_get(v_l_1790_, 0);
                v_size_1804_ = leanh::lean_ctor_get(v_r_1791_, 0);
                v_k_1805_ = leanh::lean_ctor_get(v_r_1791_, 1);
                v_v_1806_ = leanh::lean_ctor_get(v_r_1791_, 2);
                v_l_1807_ = leanh::lean_ctor_get(v_r_1791_, 3);
                v_r_1808_ = leanh::lean_ctor_get(v_r_1791_, 4);
                v___x_1809_ = leanh::lean_unsigned_to_nat(2);
                v___x_1810_ = lean_nat_mul(v___x_1809_, v_size_1803_);
                v___x_1811_ = lean_nat_dec_lt(v_size_1804_, v___x_1810_);
                leanh::lean_dec(v___x_1810_);
                if v___x_1811_ == 0 {
                    leanh::lean_inc(v_r_1808_);
                    leanh::lean_inc(v_l_1807_);
                    leanh::lean_inc(v_v_1806_);
                    leanh::lean_inc(v_k_1805_);
                    v_isSharedCheck_1840_ = (!leanh::lean_is_exclusive(v_r_1791_)) as u8;
                    if v_isSharedCheck_1840_ == 0 {
                        v_unused_1841_ = leanh::lean_ctor_get(v_r_1791_, 4);
                        leanh::lean_dec(v_unused_1841_);
                        v_unused_1842_ = leanh::lean_ctor_get(v_r_1791_, 3);
                        leanh::lean_dec(v_unused_1842_);
                        v_unused_1843_ = leanh::lean_ctor_get(v_r_1791_, 2);
                        leanh::lean_dec(v_unused_1843_);
                        v_unused_1844_ = leanh::lean_ctor_get(v_r_1791_, 1);
                        leanh::lean_dec(v_unused_1844_);
                        v_unused_1845_ = leanh::lean_ctor_get(v_r_1791_, 0);
                        leanh::lean_dec(v_unused_1845_);
                        v___x_1813_ = v_r_1791_;
                        v_isShared_1814_ = v_isSharedCheck_1840_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_1791_);
                        v___x_1813_ = leanh::lean_box(0);
                        v_isShared_1814_ = v_isSharedCheck_1840_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1778_);
                    v___x_1846_ = lean_nat_add(v___x_1785_, v_size_1787_);
                    leanh::lean_dec(v_size_1787_);
                    v___x_1847_ = lean_nat_add(v___x_1846_, v_size_1786_);
                    leanh::lean_dec(v___x_1846_);
                    v___x_1848_ = lean_nat_add(v___x_1785_, v_size_1786_);
                    leanh::lean_dec(v_size_1786_);
                    v___x_1849_ = lean_nat_add(v___x_1848_, v_size_1804_);
                    leanh::lean_dec(v___x_1848_);
                    leanh::lean_inc_ref(v_impl_1784_);
                    if v_isShared_1802_ == 0 {
                        leanh::lean_ctor_set(v___x_1801_, 4, v_impl_1784_);
                        leanh::lean_ctor_set(v___x_1801_, 3, v_r_1791_);
                        leanh::lean_ctor_set(v___x_1801_, 2, v_v_1774_);
                        leanh::lean_ctor_set(v___x_1801_, 1, v_k_1773_);
                        leanh::lean_ctor_set(v___x_1801_, 0, v___x_1849_);
                        v___x_1851_ = v___x_1801_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1864_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1849_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_k_1773_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 2, v_v_1774_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 3, v_r_1791_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 4, v_impl_1784_);
                        v___x_1851_ = v_reuseFailAlloc_1864_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1815_ = lean_nat_add(v___x_1785_, v_size_1787_);
                leanh::lean_dec(v_size_1787_);
                v___x_1816_ = lean_nat_add(v___x_1815_, v_size_1786_);
                leanh::lean_dec(v___x_1815_);
                v___x_1828_ = lean_nat_add(v___x_1785_, v_size_1803_);
                if leanh::lean_obj_tag(v_l_1807_) == 0 {
                    v_size_1838_ = leanh::lean_ctor_get(v_l_1807_, 0);
                    leanh::lean_inc(v_size_1838_);
                    v___y_1830_ = v_size_1838_;
                    state = 8;
                    continue;
                } else {
                    v___x_1839_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1830_ = v___x_1839_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1821_ = lean_nat_add(v___y_1818_, v___y_1820_);
                leanh::lean_dec(v___y_1820_);
                leanh::lean_dec(v___y_1818_);
                if v_isShared_1814_ == 0 {
                    leanh::lean_ctor_set(v___x_1813_, 4, v_impl_1784_);
                    leanh::lean_ctor_set(v___x_1813_, 3, v_r_1808_);
                    leanh::lean_ctor_set(v___x_1813_, 2, v_v_1774_);
                    leanh::lean_ctor_set(v___x_1813_, 1, v_k_1773_);
                    leanh::lean_ctor_set(v___x_1813_, 0, v___x_1821_);
                    v___x_1823_ = v___x_1813_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1827_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1821_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_k_1773_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_v_1774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_r_1808_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_impl_1784_);
                    v___x_1823_ = v_reuseFailAlloc_1827_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1802_ == 0 {
                    leanh::lean_ctor_set(v___x_1801_, 4, v___x_1823_);
                    leanh::lean_ctor_set(v___x_1801_, 3, v___y_1819_);
                    leanh::lean_ctor_set(v___x_1801_, 2, v_v_1806_);
                    leanh::lean_ctor_set(v___x_1801_, 1, v_k_1805_);
                    leanh::lean_ctor_set(v___x_1801_, 0, v___x_1816_);
                    v___x_1825_ = v___x_1801_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1826_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_k_1805_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 2, v_v_1806_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 3, v___y_1819_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 4, v___x_1823_);
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
                leanh::lean_dec(v___y_1830_);
                leanh::lean_dec(v___x_1828_);
                if v_isShared_1779_ == 0 {
                    leanh::lean_ctor_set(v___x_1778_, 4, v_l_1807_);
                    leanh::lean_ctor_set(v___x_1778_, 3, v_l_1790_);
                    leanh::lean_ctor_set(v___x_1778_, 2, v_v_1789_);
                    leanh::lean_ctor_set(v___x_1778_, 1, v_k_1788_);
                    leanh::lean_ctor_set(v___x_1778_, 0, v___x_1831_);
                    v___x_1833_ = v___x_1778_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1837_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1831_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_k_1788_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 2, v_v_1789_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 3, v_l_1790_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 4, v_l_1807_);
                    v___x_1833_ = v_reuseFailAlloc_1837_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1834_ = lean_nat_add(v___x_1785_, v_size_1786_);
                leanh::lean_dec(v_size_1786_);
                if leanh::lean_obj_tag(v_r_1808_) == 0 {
                    v_size_1835_ = leanh::lean_ctor_get(v_r_1808_, 0);
                    leanh::lean_inc(v_size_1835_);
                    v___y_1818_ = v___x_1834_;
                    v___y_1819_ = v___x_1833_;
                    v___y_1820_ = v_size_1835_;
                    state = 5;
                    continue;
                } else {
                    v___x_1836_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1818_ = v___x_1834_;
                    v___y_1819_ = v___x_1833_;
                    v___y_1820_ = v___x_1836_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1858_ = (!leanh::lean_is_exclusive(v_impl_1784_)) as u8;
                if v_isSharedCheck_1858_ == 0 {
                    v_unused_1859_ = leanh::lean_ctor_get(v_impl_1784_, 4);
                    leanh::lean_dec(v_unused_1859_);
                    v_unused_1860_ = leanh::lean_ctor_get(v_impl_1784_, 3);
                    leanh::lean_dec(v_unused_1860_);
                    v_unused_1861_ = leanh::lean_ctor_get(v_impl_1784_, 2);
                    leanh::lean_dec(v_unused_1861_);
                    v_unused_1862_ = leanh::lean_ctor_get(v_impl_1784_, 1);
                    leanh::lean_dec(v_unused_1862_);
                    v_unused_1863_ = leanh::lean_ctor_get(v_impl_1784_, 0);
                    leanh::lean_dec(v_unused_1863_);
                    v___x_1853_ = v_impl_1784_;
                    v_isShared_1854_ = v_isSharedCheck_1858_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_impl_1784_);
                    v___x_1853_ = leanh::lean_box(0);
                    v_isShared_1854_ = v_isSharedCheck_1858_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1854_ == 0 {
                    leanh::lean_ctor_set(v___x_1853_, 4, v___x_1851_);
                    leanh::lean_ctor_set(v___x_1853_, 3, v_l_1790_);
                    leanh::lean_ctor_set(v___x_1853_, 2, v_v_1789_);
                    leanh::lean_ctor_set(v___x_1853_, 1, v_k_1788_);
                    leanh::lean_ctor_set(v___x_1853_, 0, v___x_1847_);
                    v___x_1856_ = v___x_1853_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1847_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_k_1788_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_v_1789_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_l_1790_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 4, v___x_1851_);
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
                v_size_1884_ = leanh::lean_ctor_get(v_r_1877_, 0);
                v___x_1885_ = lean_nat_add(v___x_1785_, v_size_1878_);
                leanh::lean_dec(v_size_1878_);
                v___x_1886_ = lean_nat_add(v___x_1785_, v_size_1884_);
                if v_isShared_1883_ == 0 {
                    leanh::lean_ctor_set(v___x_1882_, 4, v_impl_1784_);
                    leanh::lean_ctor_set(v___x_1882_, 3, v_r_1877_);
                    leanh::lean_ctor_set(v___x_1882_, 2, v_v_1774_);
                    leanh::lean_ctor_set(v___x_1882_, 1, v_k_1773_);
                    leanh::lean_ctor_set(v___x_1882_, 0, v___x_1886_);
                    v___x_1888_ = v___x_1882_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1892_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1886_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_k_1773_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_v_1774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 3, v_r_1877_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 4, v_impl_1784_);
                    v___x_1888_ = v_reuseFailAlloc_1892_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1779_ == 0 {
                    leanh::lean_ctor_set(v___x_1778_, 4, v___x_1888_);
                    leanh::lean_ctor_set(v___x_1778_, 3, v_l_1876_);
                    leanh::lean_ctor_set(v___x_1778_, 2, v_v_1880_);
                    leanh::lean_ctor_set(v___x_1778_, 1, v_k_1879_);
                    leanh::lean_ctor_set(v___x_1778_, 0, v___x_1885_);
                    v___x_1890_ = v___x_1778_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1891_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_k_1879_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1891_, 2, v_v_1880_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1891_, 3, v_l_1876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1891_, 4, v___x_1888_);
                    v___x_1890_ = v_reuseFailAlloc_1891_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1890_;
            }
            17 => {
                v___x_1901_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_1900_ == 0 {
                    leanh::lean_ctor_set(v___x_1899_, 3, v_r_1877_);
                    leanh::lean_ctor_set(v___x_1899_, 2, v_v_1774_);
                    leanh::lean_ctor_set(v___x_1899_, 1, v_k_1773_);
                    leanh::lean_ctor_set(v___x_1899_, 0, v___x_1785_);
                    v___x_1903_ = v___x_1899_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1907_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_k_1773_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 2, v_v_1774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 3, v_r_1877_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 4, v_r_1877_);
                    v___x_1903_ = v_reuseFailAlloc_1907_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1779_ == 0 {
                    leanh::lean_ctor_set(v___x_1778_, 4, v___x_1903_);
                    leanh::lean_ctor_set(v___x_1778_, 3, v_l_1876_);
                    leanh::lean_ctor_set(v___x_1778_, 2, v_v_1897_);
                    leanh::lean_ctor_set(v___x_1778_, 1, v_k_1896_);
                    leanh::lean_ctor_set(v___x_1778_, 0, v___x_1901_);
                    v___x_1905_ = v___x_1778_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1906_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1901_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_k_1896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 2, v_v_1897_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 3, v_l_1876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 4, v___x_1903_);
                    v___x_1905_ = v_reuseFailAlloc_1906_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1905_;
            }
            20 => {
                v_k_1918_ = leanh::lean_ctor_get(v_r_1912_, 1);
                v_v_1919_ = leanh::lean_ctor_get(v_r_1912_, 2);
                v_isSharedCheck_1933_ = (!leanh::lean_is_exclusive(v_r_1912_)) as u8;
                if v_isSharedCheck_1933_ == 0 {
                    v_unused_1934_ = leanh::lean_ctor_get(v_r_1912_, 4);
                    leanh::lean_dec(v_unused_1934_);
                    v_unused_1935_ = leanh::lean_ctor_get(v_r_1912_, 3);
                    leanh::lean_dec(v_unused_1935_);
                    v_unused_1936_ = leanh::lean_ctor_get(v_r_1912_, 0);
                    leanh::lean_dec(v_unused_1936_);
                    v___x_1921_ = v_r_1912_;
                    v_isShared_1922_ = v_isSharedCheck_1933_;
                    state = 21;
                    continue;
                } else {
                    leanh::lean_inc(v_v_1919_);
                    leanh::lean_inc(v_k_1918_);
                    leanh::lean_dec(v_r_1912_);
                    v___x_1921_ = leanh::lean_box(0);
                    v_isShared_1922_ = v_isSharedCheck_1933_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_1923_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_1922_ == 0 {
                    leanh::lean_ctor_set(v___x_1921_, 4, v_l_1876_);
                    leanh::lean_ctor_set(v___x_1921_, 3, v_l_1876_);
                    leanh::lean_ctor_set(v___x_1921_, 2, v_v_1914_);
                    leanh::lean_ctor_set(v___x_1921_, 1, v_k_1913_);
                    leanh::lean_ctor_set(v___x_1921_, 0, v___x_1785_);
                    v___x_1925_ = v___x_1921_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1932_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_k_1913_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 2, v_v_1914_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 3, v_l_1876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 4, v_l_1876_);
                    v___x_1925_ = v_reuseFailAlloc_1932_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_1917_ == 0 {
                    leanh::lean_ctor_set(v___x_1916_, 4, v_l_1876_);
                    leanh::lean_ctor_set(v___x_1916_, 2, v_v_1774_);
                    leanh::lean_ctor_set(v___x_1916_, 1, v_k_1773_);
                    leanh::lean_ctor_set(v___x_1916_, 0, v___x_1785_);
                    v___x_1927_ = v___x_1916_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1931_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_k_1773_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_v_1774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_l_1876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_l_1876_);
                    v___x_1927_ = v_reuseFailAlloc_1931_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_1779_ == 0 {
                    leanh::lean_ctor_set(v___x_1778_, 4, v___x_1927_);
                    leanh::lean_ctor_set(v___x_1778_, 3, v___x_1925_);
                    leanh::lean_ctor_set(v___x_1778_, 2, v_v_1919_);
                    leanh::lean_ctor_set(v___x_1778_, 1, v_k_1918_);
                    leanh::lean_ctor_set(v___x_1778_, 0, v___x_1923_);
                    v___x_1929_ = v___x_1778_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1930_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1923_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_k_1918_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_v_1919_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 3, v___x_1925_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 4, v___x_1927_);
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
                v_tree_1964_ = leanh::lean_ctor_get(v___x_1963_, 2);
                leanh::lean_inc(v_tree_1964_);
                if leanh::lean_obj_tag(v_tree_1964_) == 0 {
                    v_k_1965_ = leanh::lean_ctor_get(v___x_1963_, 0);
                    leanh::lean_inc(v_k_1965_);
                    v_v_1966_ = leanh::lean_ctor_get(v___x_1963_, 1);
                    leanh::lean_inc(v_v_1966_);
                    leanh::lean_dec_ref(v___x_1963_);
                    v_size_1967_ = leanh::lean_ctor_get(v_tree_1964_, 0);
                    v___x_1968_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1969_ = lean_nat_mul(v___x_1968_, v_size_1967_);
                    v___x_1970_ = lean_nat_dec_lt(v___x_1969_, v_size_1953_);
                    leanh::lean_dec(v___x_1969_);
                    if v___x_1970_ == 0 {
                        leanh::lean_dec(v_l_1956_);
                        v___x_1971_ = lean_nat_add(v___x_1958_, v_size_1967_);
                        v___x_1972_ = lean_nat_add(v___x_1971_, v_size_1953_);
                        leanh::lean_dec(v___x_1971_);
                        if v_isShared_1962_ == 0 {
                            leanh::lean_ctor_set(v___x_1961_, 4, v_r_1776_);
                            leanh::lean_ctor_set(v___x_1961_, 3, v_tree_1964_);
                            leanh::lean_ctor_set(v___x_1961_, 2, v_v_1966_);
                            leanh::lean_ctor_set(v___x_1961_, 1, v_k_1965_);
                            leanh::lean_ctor_set(v___x_1961_, 0, v___x_1972_);
                            v___x_1974_ = v___x_1961_;
                            state = 28;
                            continue;
                        } else {
                            v_reuseFailAlloc_1975_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_k_1965_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1975_, 2, v_v_1966_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1975_, 3, v_tree_1964_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1975_, 4, v_r_1776_);
                            v___x_1974_ = v_reuseFailAlloc_1975_;
                            state = 28;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_r_1957_);
                        leanh::lean_inc(v_v_1955_);
                        leanh::lean_inc(v_k_1954_);
                        leanh::lean_inc(v_size_1953_);
                        v_isSharedCheck_2030_ = (!leanh::lean_is_exclusive(v_r_1776_)) as u8;
                        if v_isSharedCheck_2030_ == 0 {
                            v_unused_2031_ = leanh::lean_ctor_get(v_r_1776_, 4);
                            leanh::lean_dec(v_unused_2031_);
                            v_unused_2032_ = leanh::lean_ctor_get(v_r_1776_, 3);
                            leanh::lean_dec(v_unused_2032_);
                            v_unused_2033_ = leanh::lean_ctor_get(v_r_1776_, 2);
                            leanh::lean_dec(v_unused_2033_);
                            v_unused_2034_ = leanh::lean_ctor_get(v_r_1776_, 1);
                            leanh::lean_dec(v_unused_2034_);
                            v_unused_2035_ = leanh::lean_ctor_get(v_r_1776_, 0);
                            leanh::lean_dec(v_unused_2035_);
                            v___x_1977_ = v_r_1776_;
                            v_isShared_1978_ = v_isSharedCheck_2030_;
                            state = 29;
                            continue;
                        } else {
                            leanh::lean_dec(v_r_1776_);
                            v___x_1977_ = leanh::lean_box(0);
                            v_isShared_1978_ = v_isSharedCheck_2030_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_r_1957_);
                    leanh::lean_inc(v_v_1955_);
                    leanh::lean_inc(v_k_1954_);
                    leanh::lean_inc(v_size_1953_);
                    v_isSharedCheck_2089_ = (!leanh::lean_is_exclusive(v_r_1776_)) as u8;
                    if v_isSharedCheck_2089_ == 0 {
                        v_unused_2090_ = leanh::lean_ctor_get(v_r_1776_, 4);
                        leanh::lean_dec(v_unused_2090_);
                        v_unused_2091_ = leanh::lean_ctor_get(v_r_1776_, 3);
                        leanh::lean_dec(v_unused_2091_);
                        v_unused_2092_ = leanh::lean_ctor_get(v_r_1776_, 2);
                        leanh::lean_dec(v_unused_2092_);
                        v_unused_2093_ = leanh::lean_ctor_get(v_r_1776_, 1);
                        leanh::lean_dec(v_unused_2093_);
                        v_unused_2094_ = leanh::lean_ctor_get(v_r_1776_, 0);
                        leanh::lean_dec(v_unused_2094_);
                        v___x_2037_ = v_r_1776_;
                        v_isShared_2038_ = v_isSharedCheck_2089_;
                        state = 38;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_1776_);
                        v___x_2037_ = leanh::lean_box(0);
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
                v_size_1979_ = leanh::lean_ctor_get(v_l_1956_, 0);
                v_k_1980_ = leanh::lean_ctor_get(v_l_1956_, 1);
                v_v_1981_ = leanh::lean_ctor_get(v_l_1956_, 2);
                v_l_1982_ = leanh::lean_ctor_get(v_l_1956_, 3);
                v_r_1983_ = leanh::lean_ctor_get(v_l_1956_, 4);
                v_size_1984_ = leanh::lean_ctor_get(v_r_1957_, 0);
                v___x_1985_ = leanh::lean_unsigned_to_nat(2);
                v___x_1986_ = lean_nat_mul(v___x_1985_, v_size_1984_);
                v___x_1987_ = lean_nat_dec_lt(v_size_1979_, v___x_1986_);
                leanh::lean_dec(v___x_1986_);
                if v___x_1987_ == 0 {
                    leanh::lean_inc(v_r_1983_);
                    leanh::lean_inc(v_l_1982_);
                    leanh::lean_inc(v_v_1981_);
                    leanh::lean_inc(v_k_1980_);
                    v_isSharedCheck_2015_ = (!leanh::lean_is_exclusive(v_l_1956_)) as u8;
                    if v_isSharedCheck_2015_ == 0 {
                        v_unused_2016_ = leanh::lean_ctor_get(v_l_1956_, 4);
                        leanh::lean_dec(v_unused_2016_);
                        v_unused_2017_ = leanh::lean_ctor_get(v_l_1956_, 3);
                        leanh::lean_dec(v_unused_2017_);
                        v_unused_2018_ = leanh::lean_ctor_get(v_l_1956_, 2);
                        leanh::lean_dec(v_unused_2018_);
                        v_unused_2019_ = leanh::lean_ctor_get(v_l_1956_, 1);
                        leanh::lean_dec(v_unused_2019_);
                        v_unused_2020_ = leanh::lean_ctor_get(v_l_1956_, 0);
                        leanh::lean_dec(v_unused_2020_);
                        v___x_1989_ = v_l_1956_;
                        v_isShared_1990_ = v_isSharedCheck_2015_;
                        state = 30;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_1956_);
                        v___x_1989_ = leanh::lean_box(0);
                        v_isShared_1990_ = v_isSharedCheck_2015_;
                        state = 30;
                        continue;
                    }
                } else {
                    v___x_2021_ = lean_nat_add(v___x_1958_, v_size_1967_);
                    v___x_2022_ = lean_nat_add(v___x_2021_, v_size_1953_);
                    leanh::lean_dec(v_size_1953_);
                    v___x_2023_ = lean_nat_add(v___x_2021_, v_size_1979_);
                    leanh::lean_dec(v___x_2021_);
                    if v_isShared_1978_ == 0 {
                        leanh::lean_ctor_set(v___x_1977_, 4, v_l_1956_);
                        leanh::lean_ctor_set(v___x_1977_, 3, v_tree_1964_);
                        leanh::lean_ctor_set(v___x_1977_, 2, v_v_1966_);
                        leanh::lean_ctor_set(v___x_1977_, 1, v_k_1965_);
                        leanh::lean_ctor_set(v___x_1977_, 0, v___x_2023_);
                        v___x_2025_ = v___x_1977_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_2029_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2023_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_k_1965_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 2, v_v_1966_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 3, v_tree_1964_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 4, v_l_1956_);
                        v___x_2025_ = v_reuseFailAlloc_2029_;
                        state = 36;
                        continue;
                    }
                }
            }
            30 => {
                v___x_1991_ = lean_nat_add(v___x_1958_, v_size_1967_);
                v___x_1992_ = lean_nat_add(v___x_1991_, v_size_1953_);
                leanh::lean_dec(v_size_1953_);
                if leanh::lean_obj_tag(v_l_1982_) == 0 {
                    v_size_2013_ = leanh::lean_ctor_get(v_l_1982_, 0);
                    leanh::lean_inc(v_size_2013_);
                    v___y_2005_ = v_size_2013_;
                    state = 34;
                    continue;
                } else {
                    v___x_2014_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2005_ = v___x_2014_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_1997_ = lean_nat_add(v___y_1995_, v___y_1996_);
                leanh::lean_dec(v___y_1996_);
                leanh::lean_dec(v___y_1995_);
                if v_isShared_1990_ == 0 {
                    leanh::lean_ctor_set(v___x_1989_, 4, v_r_1957_);
                    leanh::lean_ctor_set(v___x_1989_, 3, v_r_1983_);
                    leanh::lean_ctor_set(v___x_1989_, 2, v_v_1955_);
                    leanh::lean_ctor_set(v___x_1989_, 1, v_k_1954_);
                    leanh::lean_ctor_set(v___x_1989_, 0, v___x_1997_);
                    v___x_1999_ = v___x_1989_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_k_1954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_v_1955_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_r_1983_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 4, v_r_1957_);
                    v___x_1999_ = v_reuseFailAlloc_2003_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1978_ == 0 {
                    leanh::lean_ctor_set(v___x_1977_, 4, v___x_1999_);
                    leanh::lean_ctor_set(v___x_1977_, 3, v___y_1994_);
                    leanh::lean_ctor_set(v___x_1977_, 2, v_v_1981_);
                    leanh::lean_ctor_set(v___x_1977_, 1, v_k_1980_);
                    leanh::lean_ctor_set(v___x_1977_, 0, v___x_1992_);
                    v___x_2001_ = v___x_1977_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2002_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1992_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_k_1980_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_v_1981_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 3, v___y_1994_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 4, v___x_1999_);
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
                leanh::lean_dec(v___y_2005_);
                leanh::lean_dec(v___x_1991_);
                if v_isShared_1962_ == 0 {
                    leanh::lean_ctor_set(v___x_1961_, 4, v_l_1982_);
                    leanh::lean_ctor_set(v___x_1961_, 3, v_tree_1964_);
                    leanh::lean_ctor_set(v___x_1961_, 2, v_v_1966_);
                    leanh::lean_ctor_set(v___x_1961_, 1, v_k_1965_);
                    leanh::lean_ctor_set(v___x_1961_, 0, v___x_2006_);
                    v___x_2008_ = v___x_1961_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2012_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2006_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_k_1965_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_v_1966_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 3, v_tree_1964_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 4, v_l_1982_);
                    v___x_2008_ = v_reuseFailAlloc_2012_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_2009_ = lean_nat_add(v___x_1958_, v_size_1984_);
                if leanh::lean_obj_tag(v_r_1983_) == 0 {
                    v_size_2010_ = leanh::lean_ctor_get(v_r_1983_, 0);
                    leanh::lean_inc(v_size_2010_);
                    v___y_1994_ = v___x_2008_;
                    v___y_1995_ = v___x_2009_;
                    v___y_1996_ = v_size_2010_;
                    state = 31;
                    continue;
                } else {
                    v___x_2011_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1994_ = v___x_2008_;
                    v___y_1995_ = v___x_2009_;
                    v___y_1996_ = v___x_2011_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                if v_isShared_1962_ == 0 {
                    leanh::lean_ctor_set(v___x_1961_, 4, v_r_1957_);
                    leanh::lean_ctor_set(v___x_1961_, 3, v___x_2025_);
                    leanh::lean_ctor_set(v___x_1961_, 2, v_v_1955_);
                    leanh::lean_ctor_set(v___x_1961_, 1, v_k_1954_);
                    leanh::lean_ctor_set(v___x_1961_, 0, v___x_2022_);
                    v___x_2027_ = v___x_1961_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2028_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2022_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_k_1954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2028_, 2, v_v_1955_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2028_, 3, v___x_2025_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2028_, 4, v_r_1957_);
                    v___x_2027_ = v_reuseFailAlloc_2028_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_2027_;
            }
            38 => {
                if leanh::lean_obj_tag(v_l_1956_) == 0 {
                    if leanh::lean_obj_tag(v_r_1957_) == 0 {
                        v_k_2039_ = leanh::lean_ctor_get(v___x_1963_, 0);
                        leanh::lean_inc(v_k_2039_);
                        v_v_2040_ = leanh::lean_ctor_get(v___x_1963_, 1);
                        leanh::lean_inc(v_v_2040_);
                        leanh::lean_dec_ref(v___x_1963_);
                        v_size_2041_ = leanh::lean_ctor_get(v_l_1956_, 0);
                        v___x_2042_ = lean_nat_add(v___x_1958_, v_size_1953_);
                        leanh::lean_dec(v_size_1953_);
                        v___x_2043_ = lean_nat_add(v___x_1958_, v_size_2041_);
                        if v_isShared_2038_ == 0 {
                            leanh::lean_ctor_set(v___x_2037_, 4, v_l_1956_);
                            leanh::lean_ctor_set(v___x_2037_, 3, v_tree_1964_);
                            leanh::lean_ctor_set(v___x_2037_, 2, v_v_2040_);
                            leanh::lean_ctor_set(v___x_2037_, 1, v_k_2039_);
                            leanh::lean_ctor_set(v___x_2037_, 0, v___x_2043_);
                            v___x_2045_ = v___x_2037_;
                            state = 39;
                            continue;
                        } else {
                            v_reuseFailAlloc_2049_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2043_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_k_2039_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_v_2040_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 3, v_tree_1964_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 4, v_l_1956_);
                            v___x_2045_ = v_reuseFailAlloc_2049_;
                            state = 39;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_size_1953_);
                        v_k_2050_ = leanh::lean_ctor_get(v___x_1963_, 0);
                        leanh::lean_inc(v_k_2050_);
                        v_v_2051_ = leanh::lean_ctor_get(v___x_1963_, 1);
                        leanh::lean_inc(v_v_2051_);
                        leanh::lean_dec_ref(v___x_1963_);
                        v_k_2052_ = leanh::lean_ctor_get(v_l_1956_, 1);
                        v_v_2053_ = leanh::lean_ctor_get(v_l_1956_, 2);
                        v_isSharedCheck_2067_ = (!leanh::lean_is_exclusive(v_l_1956_)) as u8;
                        if v_isSharedCheck_2067_ == 0 {
                            v_unused_2068_ = leanh::lean_ctor_get(v_l_1956_, 4);
                            leanh::lean_dec(v_unused_2068_);
                            v_unused_2069_ = leanh::lean_ctor_get(v_l_1956_, 3);
                            leanh::lean_dec(v_unused_2069_);
                            v_unused_2070_ = leanh::lean_ctor_get(v_l_1956_, 0);
                            leanh::lean_dec(v_unused_2070_);
                            v___x_2055_ = v_l_1956_;
                            v_isShared_2056_ = v_isSharedCheck_2067_;
                            state = 41;
                            continue;
                        } else {
                            leanh::lean_inc(v_v_2053_);
                            leanh::lean_inc(v_k_2052_);
                            leanh::lean_dec(v_l_1956_);
                            v___x_2055_ = leanh::lean_box(0);
                            v_isShared_2056_ = v_isSharedCheck_2067_;
                            state = 41;
                            continue;
                        }
                    }
                } else {
                    if leanh::lean_obj_tag(v_r_1957_) == 0 {
                        leanh::lean_dec(v_size_1953_);
                        v_k_2071_ = leanh::lean_ctor_get(v___x_1963_, 0);
                        leanh::lean_inc(v_k_2071_);
                        v_v_2072_ = leanh::lean_ctor_get(v___x_1963_, 1);
                        leanh::lean_inc(v_v_2072_);
                        leanh::lean_dec_ref(v___x_1963_);
                        v___x_2073_ = leanh::lean_unsigned_to_nat(3);
                        if v_isShared_2038_ == 0 {
                            leanh::lean_ctor_set(v___x_2037_, 4, v_l_1956_);
                            leanh::lean_ctor_set(v___x_2037_, 2, v_v_2072_);
                            leanh::lean_ctor_set(v___x_2037_, 1, v_k_2071_);
                            leanh::lean_ctor_set(v___x_2037_, 0, v___x_1958_);
                            v___x_2075_ = v___x_2037_;
                            state = 45;
                            continue;
                        } else {
                            v_reuseFailAlloc_2079_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_1958_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_k_2071_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_v_2072_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_l_1956_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 4, v_l_1956_);
                            v___x_2075_ = v_reuseFailAlloc_2079_;
                            state = 45;
                            continue;
                        }
                    } else {
                        v_k_2080_ = leanh::lean_ctor_get(v___x_1963_, 0);
                        leanh::lean_inc(v_k_2080_);
                        v_v_2081_ = leanh::lean_ctor_get(v___x_1963_, 1);
                        leanh::lean_inc(v_v_2081_);
                        leanh::lean_dec_ref(v___x_1963_);
                        if v_isShared_2038_ == 0 {
                            leanh::lean_ctor_set(v___x_2037_, 3, v_r_1957_);
                            v___x_2083_ = v___x_2037_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_2088_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_size_1953_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_k_1954_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 2, v_v_1955_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 3, v_r_1957_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 4, v_r_1957_);
                            v___x_2083_ = v_reuseFailAlloc_2088_;
                            state = 47;
                            continue;
                        }
                    }
                }
            }
            39 => {
                if v_isShared_1962_ == 0 {
                    leanh::lean_ctor_set(v___x_1961_, 4, v_r_1957_);
                    leanh::lean_ctor_set(v___x_1961_, 3, v___x_2045_);
                    leanh::lean_ctor_set(v___x_1961_, 2, v_v_1955_);
                    leanh::lean_ctor_set(v___x_1961_, 1, v_k_1954_);
                    leanh::lean_ctor_set(v___x_1961_, 0, v___x_2042_);
                    v___x_2047_ = v___x_1961_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2048_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2042_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_k_1954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_v_1955_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 3, v___x_2045_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 4, v_r_1957_);
                    v___x_2047_ = v_reuseFailAlloc_2048_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_2047_;
            }
            41 => {
                v___x_2057_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_2056_ == 0 {
                    leanh::lean_ctor_set(v___x_2055_, 4, v_r_1957_);
                    leanh::lean_ctor_set(v___x_2055_, 3, v_r_1957_);
                    leanh::lean_ctor_set(v___x_2055_, 2, v_v_2051_);
                    leanh::lean_ctor_set(v___x_2055_, 1, v_k_2050_);
                    leanh::lean_ctor_set(v___x_2055_, 0, v___x_1958_);
                    v___x_2059_ = v___x_2055_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2066_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_1958_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_k_2050_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 2, v_v_2051_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 3, v_r_1957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 4, v_r_1957_);
                    v___x_2059_ = v_reuseFailAlloc_2066_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                if v_isShared_2038_ == 0 {
                    leanh::lean_ctor_set(v___x_2037_, 3, v_r_1957_);
                    leanh::lean_ctor_set(v___x_2037_, 0, v___x_1958_);
                    v___x_2061_ = v___x_2037_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_2065_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_1958_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_k_1954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 2, v_v_1955_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 3, v_r_1957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 4, v_r_1957_);
                    v___x_2061_ = v_reuseFailAlloc_2065_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                if v_isShared_1962_ == 0 {
                    leanh::lean_ctor_set(v___x_1961_, 4, v___x_2061_);
                    leanh::lean_ctor_set(v___x_1961_, 3, v___x_2059_);
                    leanh::lean_ctor_set(v___x_1961_, 2, v_v_2053_);
                    leanh::lean_ctor_set(v___x_1961_, 1, v_k_2052_);
                    leanh::lean_ctor_set(v___x_1961_, 0, v___x_2057_);
                    v___x_2063_ = v___x_1961_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2064_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2057_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_k_2052_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 2, v_v_2053_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 3, v___x_2059_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 4, v___x_2061_);
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
                    leanh::lean_ctor_set(v___x_1961_, 4, v_r_1957_);
                    leanh::lean_ctor_set(v___x_1961_, 3, v___x_2075_);
                    leanh::lean_ctor_set(v___x_1961_, 2, v_v_1955_);
                    leanh::lean_ctor_set(v___x_1961_, 1, v_k_1954_);
                    leanh::lean_ctor_set(v___x_1961_, 0, v___x_2073_);
                    v___x_2077_ = v___x_1961_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2078_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2073_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_k_1954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 2, v_v_1955_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 3, v___x_2075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 4, v_r_1957_);
                    v___x_2077_ = v_reuseFailAlloc_2078_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_2077_;
            }
            47 => {
                v___x_2084_ = leanh::lean_unsigned_to_nat(2);
                if v_isShared_1962_ == 0 {
                    leanh::lean_ctor_set(v___x_1961_, 4, v___x_2083_);
                    leanh::lean_ctor_set(v___x_1961_, 3, v_r_1957_);
                    leanh::lean_ctor_set(v___x_1961_, 2, v_v_2081_);
                    leanh::lean_ctor_set(v___x_1961_, 1, v_k_2080_);
                    leanh::lean_ctor_set(v___x_1961_, 0, v___x_2084_);
                    v___x_2086_ = v___x_1961_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_2087_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_k_2080_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_v_2081_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 3, v_r_1957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 4, v___x_2083_);
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
                v_tree_2105_ = leanh::lean_ctor_get(v___x_2104_, 2);
                leanh::lean_inc(v_tree_2105_);
                if leanh::lean_obj_tag(v_tree_2105_) == 0 {
                    v_k_2106_ = leanh::lean_ctor_get(v___x_2104_, 0);
                    leanh::lean_inc(v_k_2106_);
                    v_v_2107_ = leanh::lean_ctor_get(v___x_2104_, 1);
                    leanh::lean_inc(v_v_2107_);
                    leanh::lean_dec_ref(v___x_2104_);
                    v_size_2108_ = leanh::lean_ctor_get(v_tree_2105_, 0);
                    v___x_2109_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2110_ = lean_nat_mul(v___x_2109_, v_size_2108_);
                    v___x_2111_ = lean_nat_dec_lt(v___x_2110_, v_size_1948_);
                    leanh::lean_dec(v___x_2110_);
                    if v___x_2111_ == 0 {
                        leanh::lean_dec(v_r_1952_);
                        v___x_2112_ = lean_nat_add(v___x_1958_, v_size_1948_);
                        v___x_2113_ = lean_nat_add(v___x_2112_, v_size_2108_);
                        leanh::lean_dec(v___x_2112_);
                        if v_isShared_2103_ == 0 {
                            leanh::lean_ctor_set(v___x_2102_, 4, v_tree_2105_);
                            leanh::lean_ctor_set(v___x_2102_, 3, v_l_1775_);
                            leanh::lean_ctor_set(v___x_2102_, 2, v_v_2107_);
                            leanh::lean_ctor_set(v___x_2102_, 1, v_k_2106_);
                            leanh::lean_ctor_set(v___x_2102_, 0, v___x_2113_);
                            v___x_2115_ = v___x_2102_;
                            state = 50;
                            continue;
                        } else {
                            v_reuseFailAlloc_2116_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_k_2106_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_v_2107_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 3, v_l_1775_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 4, v_tree_2105_);
                            v___x_2115_ = v_reuseFailAlloc_2116_;
                            state = 50;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_l_1951_);
                        leanh::lean_inc(v_v_1950_);
                        leanh::lean_inc(v_k_1949_);
                        leanh::lean_inc(v_size_1948_);
                        v_isSharedCheck_2182_ = (!leanh::lean_is_exclusive(v_l_1775_)) as u8;
                        if v_isSharedCheck_2182_ == 0 {
                            v_unused_2183_ = leanh::lean_ctor_get(v_l_1775_, 4);
                            leanh::lean_dec(v_unused_2183_);
                            v_unused_2184_ = leanh::lean_ctor_get(v_l_1775_, 3);
                            leanh::lean_dec(v_unused_2184_);
                            v_unused_2185_ = leanh::lean_ctor_get(v_l_1775_, 2);
                            leanh::lean_dec(v_unused_2185_);
                            v_unused_2186_ = leanh::lean_ctor_get(v_l_1775_, 1);
                            leanh::lean_dec(v_unused_2186_);
                            v_unused_2187_ = leanh::lean_ctor_get(v_l_1775_, 0);
                            leanh::lean_dec(v_unused_2187_);
                            v___x_2118_ = v_l_1775_;
                            v_isShared_2119_ = v_isSharedCheck_2182_;
                            state = 51;
                            continue;
                        } else {
                            leanh::lean_dec(v_l_1775_);
                            v___x_2118_ = leanh::lean_box(0);
                            v_isShared_2119_ = v_isSharedCheck_2182_;
                            state = 51;
                            continue;
                        }
                    }
                } else {
                    if leanh::lean_obj_tag(v_l_1951_) == 0 {
                        leanh::lean_inc_ref(v_l_1951_);
                        leanh::lean_inc(v_v_1950_);
                        leanh::lean_inc(v_k_1949_);
                        leanh::lean_inc(v_size_1948_);
                        v_isSharedCheck_2211_ = (!leanh::lean_is_exclusive(v_l_1775_)) as u8;
                        if v_isSharedCheck_2211_ == 0 {
                            v_unused_2212_ = leanh::lean_ctor_get(v_l_1775_, 4);
                            leanh::lean_dec(v_unused_2212_);
                            v_unused_2213_ = leanh::lean_ctor_get(v_l_1775_, 3);
                            leanh::lean_dec(v_unused_2213_);
                            v_unused_2214_ = leanh::lean_ctor_get(v_l_1775_, 2);
                            leanh::lean_dec(v_unused_2214_);
                            v_unused_2215_ = leanh::lean_ctor_get(v_l_1775_, 1);
                            leanh::lean_dec(v_unused_2215_);
                            v_unused_2216_ = leanh::lean_ctor_get(v_l_1775_, 0);
                            leanh::lean_dec(v_unused_2216_);
                            v___x_2189_ = v_l_1775_;
                            v_isShared_2190_ = v_isSharedCheck_2211_;
                            state = 61;
                            continue;
                        } else {
                            leanh::lean_dec(v_l_1775_);
                            v___x_2189_ = leanh::lean_box(0);
                            v_isShared_2190_ = v_isSharedCheck_2211_;
                            state = 61;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v_r_1952_) == 0 {
                            leanh::lean_inc(v_l_1951_);
                            leanh::lean_inc(v_v_1950_);
                            leanh::lean_inc(v_k_1949_);
                            v_isSharedCheck_2241_ =
                                (!leanh::lean_is_exclusive(v_l_1775_)) as u8;
                            if v_isSharedCheck_2241_ == 0 {
                                v_unused_2242_ = leanh::lean_ctor_get(v_l_1775_, 4);
                                leanh::lean_dec(v_unused_2242_);
                                v_unused_2243_ = leanh::lean_ctor_get(v_l_1775_, 3);
                                leanh::lean_dec(v_unused_2243_);
                                v_unused_2244_ = leanh::lean_ctor_get(v_l_1775_, 2);
                                leanh::lean_dec(v_unused_2244_);
                                v_unused_2245_ = leanh::lean_ctor_get(v_l_1775_, 1);
                                leanh::lean_dec(v_unused_2245_);
                                v_unused_2246_ = leanh::lean_ctor_get(v_l_1775_, 0);
                                leanh::lean_dec(v_unused_2246_);
                                v___x_2218_ = v_l_1775_;
                                v_isShared_2219_ = v_isSharedCheck_2241_;
                                state = 66;
                                continue;
                            } else {
                                leanh::lean_dec(v_l_1775_);
                                v___x_2218_ = leanh::lean_box(0);
                                v_isShared_2219_ = v_isSharedCheck_2241_;
                                state = 66;
                                continue;
                            }
                        } else {
                            v_k_2247_ = leanh::lean_ctor_get(v___x_2104_, 0);
                            leanh::lean_inc(v_k_2247_);
                            v_v_2248_ = leanh::lean_ctor_get(v___x_2104_, 1);
                            leanh::lean_inc(v_v_2248_);
                            leanh::lean_dec_ref(v___x_2104_);
                            v___x_2249_ = leanh::lean_unsigned_to_nat(2);
                            if v_isShared_2103_ == 0 {
                                leanh::lean_ctor_set(v___x_2102_, 4, v_r_1952_);
                                leanh::lean_ctor_set(v___x_2102_, 3, v_l_1775_);
                                leanh::lean_ctor_set(v___x_2102_, 2, v_v_2248_);
                                leanh::lean_ctor_set(v___x_2102_, 1, v_k_2247_);
                                leanh::lean_ctor_set(v___x_2102_, 0, v___x_2249_);
                                v___x_2251_ = v___x_2102_;
                                state = 71;
                                continue;
                            } else {
                                v_reuseFailAlloc_2252_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_k_2247_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 2, v_v_2248_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 3, v_l_1775_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 4, v_r_1952_);
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
                v_size_2120_ = leanh::lean_ctor_get(v_l_1951_, 0);
                v_size_2121_ = leanh::lean_ctor_get(v_r_1952_, 0);
                v_k_2122_ = leanh::lean_ctor_get(v_r_1952_, 1);
                v_v_2123_ = leanh::lean_ctor_get(v_r_1952_, 2);
                v_l_2124_ = leanh::lean_ctor_get(v_r_1952_, 3);
                v_r_2125_ = leanh::lean_ctor_get(v_r_1952_, 4);
                v___x_2126_ = leanh::lean_unsigned_to_nat(2);
                v___x_2127_ = lean_nat_mul(v___x_2126_, v_size_2120_);
                v___x_2128_ = lean_nat_dec_lt(v_size_2121_, v___x_2127_);
                leanh::lean_dec(v___x_2127_);
                if v___x_2128_ == 0 {
                    leanh::lean_inc(v_r_2125_);
                    leanh::lean_inc(v_l_2124_);
                    leanh::lean_inc(v_v_2123_);
                    leanh::lean_inc(v_k_2122_);
                    leanh::lean_del_object(v___x_2118_);
                    v_isSharedCheck_2166_ = (!leanh::lean_is_exclusive(v_r_1952_)) as u8;
                    if v_isSharedCheck_2166_ == 0 {
                        v_unused_2167_ = leanh::lean_ctor_get(v_r_1952_, 4);
                        leanh::lean_dec(v_unused_2167_);
                        v_unused_2168_ = leanh::lean_ctor_get(v_r_1952_, 3);
                        leanh::lean_dec(v_unused_2168_);
                        v_unused_2169_ = leanh::lean_ctor_get(v_r_1952_, 2);
                        leanh::lean_dec(v_unused_2169_);
                        v_unused_2170_ = leanh::lean_ctor_get(v_r_1952_, 1);
                        leanh::lean_dec(v_unused_2170_);
                        v_unused_2171_ = leanh::lean_ctor_get(v_r_1952_, 0);
                        leanh::lean_dec(v_unused_2171_);
                        v___x_2130_ = v_r_1952_;
                        v_isShared_2131_ = v_isSharedCheck_2166_;
                        state = 52;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_1952_);
                        v___x_2130_ = leanh::lean_box(0);
                        v_isShared_2131_ = v_isSharedCheck_2166_;
                        state = 52;
                        continue;
                    }
                } else {
                    v___x_2172_ = lean_nat_add(v___x_1958_, v_size_1948_);
                    leanh::lean_dec(v_size_1948_);
                    v___x_2173_ = lean_nat_add(v___x_2172_, v_size_2108_);
                    leanh::lean_dec(v___x_2172_);
                    v___x_2174_ = lean_nat_add(v___x_1958_, v_size_2108_);
                    v___x_2175_ = lean_nat_add(v___x_2174_, v_size_2121_);
                    leanh::lean_dec(v___x_2174_);
                    if v_isShared_2103_ == 0 {
                        leanh::lean_ctor_set(v___x_2102_, 4, v_tree_2105_);
                        leanh::lean_ctor_set(v___x_2102_, 3, v_r_1952_);
                        leanh::lean_ctor_set(v___x_2102_, 2, v_v_2107_);
                        leanh::lean_ctor_set(v___x_2102_, 1, v_k_2106_);
                        leanh::lean_ctor_set(v___x_2102_, 0, v___x_2175_);
                        v___x_2177_ = v___x_2102_;
                        state = 59;
                        continue;
                    } else {
                        v_reuseFailAlloc_2181_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2175_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_k_2106_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_v_2107_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 3, v_r_1952_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 4, v_tree_2105_);
                        v___x_2177_ = v_reuseFailAlloc_2181_;
                        state = 59;
                        continue;
                    }
                }
            }
            52 => {
                v___x_2132_ = lean_nat_add(v___x_1958_, v_size_1948_);
                leanh::lean_dec(v_size_1948_);
                v___x_2133_ = lean_nat_add(v___x_2132_, v_size_2108_);
                leanh::lean_dec(v___x_2132_);
                v___x_2154_ = lean_nat_add(v___x_1958_, v_size_2120_);
                if leanh::lean_obj_tag(v_l_2124_) == 0 {
                    v_size_2164_ = leanh::lean_ctor_get(v_l_2124_, 0);
                    leanh::lean_inc(v_size_2164_);
                    v___y_2156_ = v_size_2164_;
                    state = 57;
                    continue;
                } else {
                    v___x_2165_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2156_ = v___x_2165_;
                    state = 57;
                    continue;
                }
            }
            53 => {
                v___x_2138_ = lean_nat_add(v___y_2136_, v___y_2137_);
                leanh::lean_dec(v___y_2137_);
                leanh::lean_dec(v___y_2136_);
                leanh::lean_inc_ref(v_tree_2105_);
                if v_isShared_2131_ == 0 {
                    leanh::lean_ctor_set(v___x_2130_, 4, v_tree_2105_);
                    leanh::lean_ctor_set(v___x_2130_, 3, v_r_2125_);
                    leanh::lean_ctor_set(v___x_2130_, 2, v_v_2107_);
                    leanh::lean_ctor_set(v___x_2130_, 1, v_k_2106_);
                    leanh::lean_ctor_set(v___x_2130_, 0, v___x_2138_);
                    v___x_2140_ = v___x_2130_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_2153_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2138_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_k_2106_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_v_2107_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2153_, 3, v_r_2125_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2153_, 4, v_tree_2105_);
                    v___x_2140_ = v_reuseFailAlloc_2153_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                v_isSharedCheck_2147_ = (!leanh::lean_is_exclusive(v_tree_2105_)) as u8;
                if v_isSharedCheck_2147_ == 0 {
                    v_unused_2148_ = leanh::lean_ctor_get(v_tree_2105_, 4);
                    leanh::lean_dec(v_unused_2148_);
                    v_unused_2149_ = leanh::lean_ctor_get(v_tree_2105_, 3);
                    leanh::lean_dec(v_unused_2149_);
                    v_unused_2150_ = leanh::lean_ctor_get(v_tree_2105_, 2);
                    leanh::lean_dec(v_unused_2150_);
                    v_unused_2151_ = leanh::lean_ctor_get(v_tree_2105_, 1);
                    leanh::lean_dec(v_unused_2151_);
                    v_unused_2152_ = leanh::lean_ctor_get(v_tree_2105_, 0);
                    leanh::lean_dec(v_unused_2152_);
                    v___x_2142_ = v_tree_2105_;
                    v_isShared_2143_ = v_isSharedCheck_2147_;
                    state = 55;
                    continue;
                } else {
                    leanh::lean_dec(v_tree_2105_);
                    v___x_2142_ = leanh::lean_box(0);
                    v_isShared_2143_ = v_isSharedCheck_2147_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                if v_isShared_2143_ == 0 {
                    leanh::lean_ctor_set(v___x_2142_, 4, v___x_2140_);
                    leanh::lean_ctor_set(v___x_2142_, 3, v___y_2135_);
                    leanh::lean_ctor_set(v___x_2142_, 2, v_v_2123_);
                    leanh::lean_ctor_set(v___x_2142_, 1, v_k_2122_);
                    leanh::lean_ctor_set(v___x_2142_, 0, v___x_2133_);
                    v___x_2145_ = v___x_2142_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_2146_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2133_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_k_2122_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 2, v_v_2123_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 3, v___y_2135_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 4, v___x_2140_);
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
                leanh::lean_dec(v___y_2156_);
                leanh::lean_dec(v___x_2154_);
                if v_isShared_2103_ == 0 {
                    leanh::lean_ctor_set(v___x_2102_, 4, v_l_2124_);
                    leanh::lean_ctor_set(v___x_2102_, 3, v_l_1951_);
                    leanh::lean_ctor_set(v___x_2102_, 2, v_v_1950_);
                    leanh::lean_ctor_set(v___x_2102_, 1, v_k_1949_);
                    leanh::lean_ctor_set(v___x_2102_, 0, v___x_2157_);
                    v___x_2159_ = v___x_2102_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_2163_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2157_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_k_1949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_v_1950_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 3, v_l_1951_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 4, v_l_2124_);
                    v___x_2159_ = v_reuseFailAlloc_2163_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                v___x_2160_ = lean_nat_add(v___x_1958_, v_size_2108_);
                if leanh::lean_obj_tag(v_r_2125_) == 0 {
                    v_size_2161_ = leanh::lean_ctor_get(v_r_2125_, 0);
                    leanh::lean_inc(v_size_2161_);
                    v___y_2135_ = v___x_2159_;
                    v___y_2136_ = v___x_2160_;
                    v___y_2137_ = v_size_2161_;
                    state = 53;
                    continue;
                } else {
                    v___x_2162_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2135_ = v___x_2159_;
                    v___y_2136_ = v___x_2160_;
                    v___y_2137_ = v___x_2162_;
                    state = 53;
                    continue;
                }
            }
            59 => {
                if v_isShared_2119_ == 0 {
                    leanh::lean_ctor_set(v___x_2118_, 4, v___x_2177_);
                    leanh::lean_ctor_set(v___x_2118_, 0, v___x_2173_);
                    v___x_2179_ = v___x_2118_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2180_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2173_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_k_1949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_v_1950_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2180_, 3, v_l_1951_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2180_, 4, v___x_2177_);
                    v___x_2179_ = v_reuseFailAlloc_2180_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_2179_;
            }
            61 => {
                if leanh::lean_obj_tag(v_r_1952_) == 0 {
                    v_k_2191_ = leanh::lean_ctor_get(v___x_2104_, 0);
                    leanh::lean_inc(v_k_2191_);
                    v_v_2192_ = leanh::lean_ctor_get(v___x_2104_, 1);
                    leanh::lean_inc(v_v_2192_);
                    leanh::lean_dec_ref(v___x_2104_);
                    v_size_2193_ = leanh::lean_ctor_get(v_r_1952_, 0);
                    v___x_2194_ = lean_nat_add(v___x_1958_, v_size_1948_);
                    leanh::lean_dec(v_size_1948_);
                    v___x_2195_ = lean_nat_add(v___x_1958_, v_size_2193_);
                    if v_isShared_2103_ == 0 {
                        leanh::lean_ctor_set(v___x_2102_, 4, v_tree_2105_);
                        leanh::lean_ctor_set(v___x_2102_, 3, v_r_1952_);
                        leanh::lean_ctor_set(v___x_2102_, 2, v_v_2192_);
                        leanh::lean_ctor_set(v___x_2102_, 1, v_k_2191_);
                        leanh::lean_ctor_set(v___x_2102_, 0, v___x_2195_);
                        v___x_2197_ = v___x_2102_;
                        state = 62;
                        continue;
                    } else {
                        v_reuseFailAlloc_2201_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2195_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_k_2191_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_v_2192_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_r_1952_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 4, v_tree_2105_);
                        v___x_2197_ = v_reuseFailAlloc_2201_;
                        state = 62;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_size_1948_);
                    v_k_2202_ = leanh::lean_ctor_get(v___x_2104_, 0);
                    leanh::lean_inc(v_k_2202_);
                    v_v_2203_ = leanh::lean_ctor_get(v___x_2104_, 1);
                    leanh::lean_inc(v_v_2203_);
                    leanh::lean_dec_ref(v___x_2104_);
                    v___x_2204_ = leanh::lean_unsigned_to_nat(3);
                    if v_isShared_2103_ == 0 {
                        leanh::lean_ctor_set(v___x_2102_, 4, v_r_1952_);
                        leanh::lean_ctor_set(v___x_2102_, 3, v_r_1952_);
                        leanh::lean_ctor_set(v___x_2102_, 2, v_v_2203_);
                        leanh::lean_ctor_set(v___x_2102_, 1, v_k_2202_);
                        leanh::lean_ctor_set(v___x_2102_, 0, v___x_1958_);
                        v___x_2206_ = v___x_2102_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_2210_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_1958_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_k_2202_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_v_2203_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 3, v_r_1952_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 4, v_r_1952_);
                        v___x_2206_ = v_reuseFailAlloc_2210_;
                        state = 64;
                        continue;
                    }
                }
            }
            62 => {
                if v_isShared_2190_ == 0 {
                    leanh::lean_ctor_set(v___x_2189_, 4, v___x_2197_);
                    leanh::lean_ctor_set(v___x_2189_, 0, v___x_2194_);
                    v___x_2199_ = v___x_2189_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_2200_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2194_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_k_1949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_v_1950_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 3, v_l_1951_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 4, v___x_2197_);
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
                    leanh::lean_ctor_set(v___x_2189_, 4, v___x_2206_);
                    leanh::lean_ctor_set(v___x_2189_, 0, v___x_2204_);
                    v___x_2208_ = v___x_2189_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2209_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2204_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_k_1949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_v_1950_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 3, v_l_1951_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 4, v___x_2206_);
                    v___x_2208_ = v_reuseFailAlloc_2209_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_2208_;
            }
            66 => {
                v_k_2220_ = leanh::lean_ctor_get(v___x_2104_, 0);
                leanh::lean_inc(v_k_2220_);
                v_v_2221_ = leanh::lean_ctor_get(v___x_2104_, 1);
                leanh::lean_inc(v_v_2221_);
                leanh::lean_dec_ref(v___x_2104_);
                v_k_2222_ = leanh::lean_ctor_get(v_r_1952_, 1);
                v_v_2223_ = leanh::lean_ctor_get(v_r_1952_, 2);
                v_isSharedCheck_2237_ = (!leanh::lean_is_exclusive(v_r_1952_)) as u8;
                if v_isSharedCheck_2237_ == 0 {
                    v_unused_2238_ = leanh::lean_ctor_get(v_r_1952_, 4);
                    leanh::lean_dec(v_unused_2238_);
                    v_unused_2239_ = leanh::lean_ctor_get(v_r_1952_, 3);
                    leanh::lean_dec(v_unused_2239_);
                    v_unused_2240_ = leanh::lean_ctor_get(v_r_1952_, 0);
                    leanh::lean_dec(v_unused_2240_);
                    v___x_2225_ = v_r_1952_;
                    v_isShared_2226_ = v_isSharedCheck_2237_;
                    state = 67;
                    continue;
                } else {
                    leanh::lean_inc(v_v_2223_);
                    leanh::lean_inc(v_k_2222_);
                    leanh::lean_dec(v_r_1952_);
                    v___x_2225_ = leanh::lean_box(0);
                    v_isShared_2226_ = v_isSharedCheck_2237_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                v___x_2227_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_2226_ == 0 {
                    leanh::lean_ctor_set(v___x_2225_, 4, v_l_1951_);
                    leanh::lean_ctor_set(v___x_2225_, 3, v_l_1951_);
                    leanh::lean_ctor_set(v___x_2225_, 2, v_v_1950_);
                    leanh::lean_ctor_set(v___x_2225_, 1, v_k_1949_);
                    leanh::lean_ctor_set(v___x_2225_, 0, v___x_1958_);
                    v___x_2229_ = v___x_2225_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_2236_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_1958_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_k_1949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 2, v_v_1950_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 3, v_l_1951_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 4, v_l_1951_);
                    v___x_2229_ = v_reuseFailAlloc_2236_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                if v_isShared_2103_ == 0 {
                    leanh::lean_ctor_set(v___x_2102_, 4, v_l_1951_);
                    leanh::lean_ctor_set(v___x_2102_, 3, v_l_1951_);
                    leanh::lean_ctor_set(v___x_2102_, 2, v_v_2221_);
                    leanh::lean_ctor_set(v___x_2102_, 1, v_k_2220_);
                    leanh::lean_ctor_set(v___x_2102_, 0, v___x_1958_);
                    v___x_2231_ = v___x_2102_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_2235_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_1958_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_k_2220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_v_2221_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_l_1951_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 4, v_l_1951_);
                    v___x_2231_ = v_reuseFailAlloc_2235_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                if v_isShared_2219_ == 0 {
                    leanh::lean_ctor_set(v___x_2218_, 4, v___x_2231_);
                    leanh::lean_ctor_set(v___x_2218_, 3, v___x_2229_);
                    leanh::lean_ctor_set(v___x_2218_, 2, v_v_2223_);
                    leanh::lean_ctor_set(v___x_2218_, 1, v_k_2222_);
                    leanh::lean_ctor_set(v___x_2218_, 0, v___x_2227_);
                    v___x_2233_ = v___x_2218_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_2234_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2227_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_k_2222_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 2, v_v_2223_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 3, v___x_2229_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 4, v___x_2231_);
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
                v_size_2278_ = leanh::lean_ctor_get(v_l_2265_, 0);
                v_k_2279_ = leanh::lean_ctor_get(v_l_2265_, 1);
                v_v_2280_ = leanh::lean_ctor_get(v_l_2265_, 2);
                v_l_2281_ = leanh::lean_ctor_get(v_l_2265_, 3);
                v_r_2282_ = leanh::lean_ctor_get(v_l_2265_, 4);
                v_size_2283_ = leanh::lean_ctor_get(v_r_2266_, 0);
                v___x_2284_ = leanh::lean_unsigned_to_nat(2);
                v___x_2285_ = lean_nat_mul(v___x_2284_, v_size_2283_);
                v___x_2286_ = lean_nat_dec_lt(v_size_2278_, v___x_2285_);
                leanh::lean_dec(v___x_2285_);
                if v___x_2286_ == 0 {
                    leanh::lean_inc(v_r_2282_);
                    leanh::lean_inc(v_l_2281_);
                    leanh::lean_inc(v_v_2280_);
                    leanh::lean_inc(v_k_2279_);
                    v_isSharedCheck_2314_ = (!leanh::lean_is_exclusive(v_l_2265_)) as u8;
                    if v_isSharedCheck_2314_ == 0 {
                        v_unused_2315_ = leanh::lean_ctor_get(v_l_2265_, 4);
                        leanh::lean_dec(v_unused_2315_);
                        v_unused_2316_ = leanh::lean_ctor_get(v_l_2265_, 3);
                        leanh::lean_dec(v_unused_2316_);
                        v_unused_2317_ = leanh::lean_ctor_get(v_l_2265_, 2);
                        leanh::lean_dec(v_unused_2317_);
                        v_unused_2318_ = leanh::lean_ctor_get(v_l_2265_, 1);
                        leanh::lean_dec(v_unused_2318_);
                        v_unused_2319_ = leanh::lean_ctor_get(v_l_2265_, 0);
                        leanh::lean_dec(v_unused_2319_);
                        v___x_2288_ = v_l_2265_;
                        v_isShared_2289_ = v_isSharedCheck_2314_;
                        state = 74;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_2265_);
                        v___x_2288_ = leanh::lean_box(0);
                        v_isShared_2289_ = v_isSharedCheck_2314_;
                        state = 74;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1778_);
                    v___x_2320_ = lean_nat_add(v___x_2260_, v_size_2261_);
                    leanh::lean_dec(v_size_2261_);
                    v___x_2321_ = lean_nat_add(v___x_2320_, v_size_2262_);
                    leanh::lean_dec(v_size_2262_);
                    v___x_2322_ = lean_nat_add(v___x_2320_, v_size_2278_);
                    leanh::lean_dec(v___x_2320_);
                    leanh::lean_inc_ref(v_impl_2259_);
                    if v_isShared_2277_ == 0 {
                        leanh::lean_ctor_set(v___x_2276_, 4, v_l_2265_);
                        leanh::lean_ctor_set(v___x_2276_, 3, v_impl_2259_);
                        leanh::lean_ctor_set(v___x_2276_, 2, v_v_1774_);
                        leanh::lean_ctor_set(v___x_2276_, 1, v_k_1773_);
                        leanh::lean_ctor_set(v___x_2276_, 0, v___x_2322_);
                        v___x_2324_ = v___x_2276_;
                        state = 80;
                        continue;
                    } else {
                        v_reuseFailAlloc_2337_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2322_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_k_1773_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 2, v_v_1774_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 3, v_impl_2259_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 4, v_l_2265_);
                        v___x_2324_ = v_reuseFailAlloc_2337_;
                        state = 80;
                        continue;
                    }
                }
            }
            74 => {
                v___x_2290_ = lean_nat_add(v___x_2260_, v_size_2261_);
                leanh::lean_dec(v_size_2261_);
                v___x_2291_ = lean_nat_add(v___x_2290_, v_size_2262_);
                leanh::lean_dec(v_size_2262_);
                if leanh::lean_obj_tag(v_l_2281_) == 0 {
                    v_size_2312_ = leanh::lean_ctor_get(v_l_2281_, 0);
                    leanh::lean_inc(v_size_2312_);
                    v___y_2304_ = v_size_2312_;
                    state = 78;
                    continue;
                } else {
                    v___x_2313_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2304_ = v___x_2313_;
                    state = 78;
                    continue;
                }
            }
            75 => {
                v___x_2296_ = lean_nat_add(v___y_2293_, v___y_2295_);
                leanh::lean_dec(v___y_2295_);
                leanh::lean_dec(v___y_2293_);
                if v_isShared_2289_ == 0 {
                    leanh::lean_ctor_set(v___x_2288_, 4, v_r_2266_);
                    leanh::lean_ctor_set(v___x_2288_, 3, v_r_2282_);
                    leanh::lean_ctor_set(v___x_2288_, 2, v_v_2264_);
                    leanh::lean_ctor_set(v___x_2288_, 1, v_k_2263_);
                    leanh::lean_ctor_set(v___x_2288_, 0, v___x_2296_);
                    v___x_2298_ = v___x_2288_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_2302_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2296_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2302_, 1, v_k_2263_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2302_, 2, v_v_2264_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2302_, 3, v_r_2282_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2302_, 4, v_r_2266_);
                    v___x_2298_ = v_reuseFailAlloc_2302_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                if v_isShared_2277_ == 0 {
                    leanh::lean_ctor_set(v___x_2276_, 4, v___x_2298_);
                    leanh::lean_ctor_set(v___x_2276_, 3, v___y_2294_);
                    leanh::lean_ctor_set(v___x_2276_, 2, v_v_2280_);
                    leanh::lean_ctor_set(v___x_2276_, 1, v_k_2279_);
                    leanh::lean_ctor_set(v___x_2276_, 0, v___x_2291_);
                    v___x_2300_ = v___x_2276_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_2301_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2291_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_k_2279_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 2, v_v_2280_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 3, v___y_2294_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 4, v___x_2298_);
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
                leanh::lean_dec(v___y_2304_);
                leanh::lean_dec(v___x_2290_);
                if v_isShared_1779_ == 0 {
                    leanh::lean_ctor_set(v___x_1778_, 4, v_l_2281_);
                    leanh::lean_ctor_set(v___x_1778_, 3, v_impl_2259_);
                    leanh::lean_ctor_set(v___x_1778_, 0, v___x_2305_);
                    v___x_2307_ = v___x_1778_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_2311_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2305_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_k_1773_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 2, v_v_1774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 3, v_impl_2259_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 4, v_l_2281_);
                    v___x_2307_ = v_reuseFailAlloc_2311_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                v___x_2308_ = lean_nat_add(v___x_2260_, v_size_2283_);
                if leanh::lean_obj_tag(v_r_2282_) == 0 {
                    v_size_2309_ = leanh::lean_ctor_get(v_r_2282_, 0);
                    leanh::lean_inc(v_size_2309_);
                    v___y_2293_ = v___x_2308_;
                    v___y_2294_ = v___x_2307_;
                    v___y_2295_ = v_size_2309_;
                    state = 75;
                    continue;
                } else {
                    v___x_2310_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2293_ = v___x_2308_;
                    v___y_2294_ = v___x_2307_;
                    v___y_2295_ = v___x_2310_;
                    state = 75;
                    continue;
                }
            }
            80 => {
                v_isSharedCheck_2331_ = (!leanh::lean_is_exclusive(v_impl_2259_)) as u8;
                if v_isSharedCheck_2331_ == 0 {
                    v_unused_2332_ = leanh::lean_ctor_get(v_impl_2259_, 4);
                    leanh::lean_dec(v_unused_2332_);
                    v_unused_2333_ = leanh::lean_ctor_get(v_impl_2259_, 3);
                    leanh::lean_dec(v_unused_2333_);
                    v_unused_2334_ = leanh::lean_ctor_get(v_impl_2259_, 2);
                    leanh::lean_dec(v_unused_2334_);
                    v_unused_2335_ = leanh::lean_ctor_get(v_impl_2259_, 1);
                    leanh::lean_dec(v_unused_2335_);
                    v_unused_2336_ = leanh::lean_ctor_get(v_impl_2259_, 0);
                    leanh::lean_dec(v_unused_2336_);
                    v___x_2326_ = v_impl_2259_;
                    v_isShared_2327_ = v_isSharedCheck_2331_;
                    state = 81;
                    continue;
                } else {
                    leanh::lean_dec(v_impl_2259_);
                    v___x_2326_ = leanh::lean_box(0);
                    v_isShared_2327_ = v_isSharedCheck_2331_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                if v_isShared_2327_ == 0 {
                    leanh::lean_ctor_set(v___x_2326_, 4, v_r_2266_);
                    leanh::lean_ctor_set(v___x_2326_, 3, v___x_2324_);
                    leanh::lean_ctor_set(v___x_2326_, 2, v_v_2264_);
                    leanh::lean_ctor_set(v___x_2326_, 1, v_k_2263_);
                    leanh::lean_ctor_set(v___x_2326_, 0, v___x_2321_);
                    v___x_2329_ = v___x_2326_;
                    state = 82;
                    continue;
                } else {
                    v_reuseFailAlloc_2330_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2321_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_k_2263_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 2, v_v_2264_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 3, v___x_2324_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 4, v_r_2266_);
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
                v_size_2357_ = leanh::lean_ctor_get(v_l_2349_, 0);
                v___x_2358_ = lean_nat_add(v___x_2260_, v_size_2351_);
                leanh::lean_dec(v_size_2351_);
                v___x_2359_ = lean_nat_add(v___x_2260_, v_size_2357_);
                if v_isShared_2356_ == 0 {
                    leanh::lean_ctor_set(v___x_2355_, 4, v_l_2349_);
                    leanh::lean_ctor_set(v___x_2355_, 3, v_impl_2259_);
                    leanh::lean_ctor_set(v___x_2355_, 2, v_v_1774_);
                    leanh::lean_ctor_set(v___x_2355_, 1, v_k_1773_);
                    leanh::lean_ctor_set(v___x_2355_, 0, v___x_2359_);
                    v___x_2361_ = v___x_2355_;
                    state = 85;
                    continue;
                } else {
                    v_reuseFailAlloc_2365_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2359_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_k_1773_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 2, v_v_1774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 3, v_impl_2259_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 4, v_l_2349_);
                    v___x_2361_ = v_reuseFailAlloc_2365_;
                    state = 85;
                    continue;
                }
            }
            85 => {
                if v_isShared_1779_ == 0 {
                    leanh::lean_ctor_set(v___x_1778_, 4, v_r_2350_);
                    leanh::lean_ctor_set(v___x_1778_, 3, v___x_2361_);
                    leanh::lean_ctor_set(v___x_1778_, 2, v_v_2353_);
                    leanh::lean_ctor_set(v___x_1778_, 1, v_k_2352_);
                    leanh::lean_ctor_set(v___x_1778_, 0, v___x_2358_);
                    v___x_2363_ = v___x_1778_;
                    state = 86;
                    continue;
                } else {
                    v_reuseFailAlloc_2364_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2358_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_k_2352_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 2, v_v_2353_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 3, v___x_2361_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 4, v_r_2350_);
                    v___x_2363_ = v_reuseFailAlloc_2364_;
                    state = 86;
                    continue;
                }
            }
            86 => {
                return v___x_2363_;
            }
            87 => {
                v_k_2374_ = leanh::lean_ctor_get(v_l_2349_, 1);
                v_v_2375_ = leanh::lean_ctor_get(v_l_2349_, 2);
                v_isSharedCheck_2389_ = (!leanh::lean_is_exclusive(v_l_2349_)) as u8;
                if v_isSharedCheck_2389_ == 0 {
                    v_unused_2390_ = leanh::lean_ctor_get(v_l_2349_, 4);
                    leanh::lean_dec(v_unused_2390_);
                    v_unused_2391_ = leanh::lean_ctor_get(v_l_2349_, 3);
                    leanh::lean_dec(v_unused_2391_);
                    v_unused_2392_ = leanh::lean_ctor_get(v_l_2349_, 0);
                    leanh::lean_dec(v_unused_2392_);
                    v___x_2377_ = v_l_2349_;
                    v_isShared_2378_ = v_isSharedCheck_2389_;
                    state = 88;
                    continue;
                } else {
                    leanh::lean_inc(v_v_2375_);
                    leanh::lean_inc(v_k_2374_);
                    leanh::lean_dec(v_l_2349_);
                    v___x_2377_ = leanh::lean_box(0);
                    v_isShared_2378_ = v_isSharedCheck_2389_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                v___x_2379_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_2378_ == 0 {
                    leanh::lean_ctor_set(v___x_2377_, 4, v_r_2350_);
                    leanh::lean_ctor_set(v___x_2377_, 3, v_r_2350_);
                    leanh::lean_ctor_set(v___x_2377_, 2, v_v_1774_);
                    leanh::lean_ctor_set(v___x_2377_, 1, v_k_1773_);
                    leanh::lean_ctor_set(v___x_2377_, 0, v___x_2260_);
                    v___x_2381_ = v___x_2377_;
                    state = 89;
                    continue;
                } else {
                    v_reuseFailAlloc_2388_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2260_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_k_1773_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 2, v_v_1774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 3, v_r_2350_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 4, v_r_2350_);
                    v___x_2381_ = v_reuseFailAlloc_2388_;
                    state = 89;
                    continue;
                }
            }
            89 => {
                if v_isShared_2373_ == 0 {
                    leanh::lean_ctor_set(v___x_2372_, 3, v_r_2350_);
                    leanh::lean_ctor_set(v___x_2372_, 0, v___x_2260_);
                    v___x_2383_ = v___x_2372_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_2387_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2260_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 1, v_k_2369_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 2, v_v_2370_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 3, v_r_2350_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 4, v_r_2350_);
                    v___x_2383_ = v_reuseFailAlloc_2387_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_1779_ == 0 {
                    leanh::lean_ctor_set(v___x_1778_, 4, v___x_2383_);
                    leanh::lean_ctor_set(v___x_1778_, 3, v___x_2381_);
                    leanh::lean_ctor_set(v___x_1778_, 2, v_v_2375_);
                    leanh::lean_ctor_set(v___x_1778_, 1, v_k_2374_);
                    leanh::lean_ctor_set(v___x_1778_, 0, v___x_2379_);
                    v___x_2385_ = v___x_1778_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2379_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_k_2374_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 2, v_v_2375_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 3, v___x_2381_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 4, v___x_2383_);
                    v___x_2385_ = v_reuseFailAlloc_2386_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_2385_;
            }
            92 => {
                v___x_2403_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_2402_ == 0 {
                    leanh::lean_ctor_set(v___x_2401_, 4, v_l_2349_);
                    leanh::lean_ctor_set(v___x_2401_, 2, v_v_1774_);
                    leanh::lean_ctor_set(v___x_2401_, 1, v_k_1773_);
                    leanh::lean_ctor_set(v___x_2401_, 0, v___x_2260_);
                    v___x_2405_ = v___x_2401_;
                    state = 93;
                    continue;
                } else {
                    v_reuseFailAlloc_2409_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2260_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 1, v_k_1773_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 2, v_v_1774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 3, v_l_2349_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 4, v_l_2349_);
                    v___x_2405_ = v_reuseFailAlloc_2409_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                if v_isShared_1779_ == 0 {
                    leanh::lean_ctor_set(v___x_1778_, 4, v_r_2397_);
                    leanh::lean_ctor_set(v___x_1778_, 3, v___x_2405_);
                    leanh::lean_ctor_set(v___x_1778_, 2, v_v_2399_);
                    leanh::lean_ctor_set(v___x_1778_, 1, v_k_2398_);
                    leanh::lean_ctor_set(v___x_1778_, 0, v___x_2403_);
                    v___x_2407_ = v___x_1778_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_2408_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2403_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2408_, 1, v_k_2398_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2408_, 2, v_v_2399_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2408_, 3, v___x_2405_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2408_, 4, v_r_2397_);
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
                    leanh::lean_ctor_set(v___x_2418_, 3, v_r_2397_);
                    v___x_2421_ = v___x_2418_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_size_2414_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_k_2415_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 2, v_v_2416_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 3, v_r_2397_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 4, v_r_2397_);
                    v___x_2421_ = v_reuseFailAlloc_2426_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                v___x_2422_ = leanh::lean_unsigned_to_nat(2);
                if v_isShared_1779_ == 0 {
                    leanh::lean_ctor_set(v___x_1778_, 4, v___x_2421_);
                    leanh::lean_ctor_set(v___x_1778_, 3, v_r_2397_);
                    leanh::lean_ctor_set(v___x_1778_, 0, v___x_2422_);
                    v___x_2424_ = v___x_1778_;
                    state = 97;
                    continue;
                } else {
                    v_reuseFailAlloc_2425_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2422_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_k_1773_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2425_, 2, v_v_1774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2425_, 3, v_r_2397_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2425_, 4, v___x_2421_);
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
    mut v_k_2435_: *mut leanh::LeanObject,
    mut v_t_2436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_boxed_2437_: u64 = 0;
    let mut v_res_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_2437_ = leanh::lean_unbox_uint64(v_k_2435_);
    leanh::lean_dec_ref(v_k_2435_);
    v_res_2438_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_boxed_2437_, v_t_2436_);
    return v_res_2438_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(
    mut v_t_2439_: *mut leanh::LeanObject,
    mut v_k_2440_: u64,
) -> *mut leanh::LeanObject {
    let mut v_k_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u64 = 0;
    let mut v___x_2446_: u8 = 0;
    let mut v___x_2447_: u64 = 0;
    let mut v___x_2448_: u8 = 0;
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_2439_) == 0 {
                    v_k_2441_ = leanh::lean_ctor_get(v_t_2439_, 1);
                    v_v_2442_ = leanh::lean_ctor_get(v_t_2439_, 2);
                    v_l_2443_ = leanh::lean_ctor_get(v_t_2439_, 3);
                    v_r_2444_ = leanh::lean_ctor_get(v_t_2439_, 4);
                    v___x_2445_ = leanh::lean_unbox_uint64(v_k_2441_);
                    v___x_2446_ = lean_uint64_dec_lt(v_k_2440_, v___x_2445_);
                    if v___x_2446_ == 0 {
                        v___x_2447_ = leanh::lean_unbox_uint64(v_k_2441_);
                        v___x_2448_ = lean_uint64_dec_eq(v_k_2440_, v___x_2447_);
                        if v___x_2448_ == 0 {
                            v_t_2439_ = v_r_2444_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_inc(v_v_2442_);
                            v___x_2450_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2450_, 0, v_v_2442_);
                            return v___x_2450_;
                        }
                    } else {
                        v_t_2439_ = v_l_2443_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_2452_ = leanh::lean_box(0);
                    return v___x_2452_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg___boxed(
    mut v_t_2453_: *mut leanh::LeanObject,
    mut v_k_2454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_boxed_2455_: u64 = 0;
    let mut v_res_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_2455_ = leanh::lean_unbox_uint64(v_k_2454_);
    leanh::lean_dec_ref(v_k_2454_);
    v_res_2456_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_t_2453_, v_k_boxed_2455_);
    leanh::lean_dec(v_t_2453_);
    return v_res_2456_;
}
pub unsafe fn l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(
    mut v_state_2457_: *mut leanh::LeanObject,
    mut v_id_2458_: u64,
    mut v_reason_2459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tokens_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2466_: usize = 0;
    let mut v___x_2467_: usize = 0;
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tokens_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_2471_: u64 = 0;
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2474_: u8 = 0;
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tokens_2461_ = leanh::lean_ctor_get(v_state_2457_, 0);
                v___x_2462_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_tokens_2461_, v_id_2458_);
                if leanh::lean_obj_tag(v___x_2462_) == 1 {
                    v_val_2463_ = leanh::lean_ctor_get(v___x_2462_, 0);
                    leanh::lean_inc(v_val_2463_);
                    leanh::lean_dec_ref_known(v___x_2462_, 1);
                    v_fst_2464_ = leanh::lean_ctor_get(v_val_2463_, 0);
                    leanh::lean_inc(v_fst_2464_);
                    v_snd_2465_ = leanh::lean_ctor_get(v_val_2463_, 1);
                    leanh::lean_inc(v_snd_2465_);
                    leanh::lean_dec(v_val_2463_);
                    v_sz_2466_ = lean_array_size(v_snd_2465_);
                    v___x_2467_ = 0usize;
                    leanh::lean_inc(v_reason_2459_);
                    v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(v_reason_2459_, v_snd_2465_, v_sz_2466_, v___x_2467_, v_state_2457_);
                    leanh::lean_dec(v_snd_2465_);
                    v___x_2469_ = l_Std_CancellationToken_cancel(v_fst_2464_, v_reason_2459_);
                    v_tokens_2470_ = leanh::lean_ctor_get(v___x_2468_, 0);
                    v_id_2471_ = leanh::lean_ctor_get_uint64(
                        v___x_2468_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_isSharedCheck_2479_ = (!leanh::lean_is_exclusive(v___x_2468_)) as u8;
                    if v_isSharedCheck_2479_ == 0 {
                        v___x_2473_ = v___x_2468_;
                        v_isShared_2474_ = v_isSharedCheck_2479_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tokens_2470_);
                        leanh::lean_dec(v___x_2468_);
                        v___x_2473_ = leanh::lean_box(0);
                        v_isShared_2474_ = v_isSharedCheck_2479_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2462_);
                    leanh::lean_dec(v_reason_2459_);
                    return v_state_2457_;
                }
            }
            1 => {
                v___x_2475_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_id_2458_, v_tokens_2470_);
                if v_isShared_2474_ == 0 {
                    leanh::lean_ctor_set(v___x_2473_, 0, v___x_2475_);
                    v___x_2477_ = v___x_2473_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2478_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2478_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_reason_2480_: *mut leanh::LeanObject,
    mut v_as_2481_: *mut leanh::LeanObject,
    mut v_sz_2482_: usize,
    mut v_i_2483_: usize,
    mut v_b_2484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2486_: u8 = 0;
    let mut v_a_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: u64 = 0;
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: usize = 0;
    let mut v___x_2491_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2486_ = lean_usize_dec_lt(v_i_2483_, v_sz_2482_);
                if v___x_2486_ == 0 {
                    leanh::lean_dec(v_reason_2480_);
                    return v_b_2484_;
                } else {
                    v_a_2487_ = lean_array_uget_borrowed(v_as_2481_, v_i_2483_);
                    v___x_2488_ = leanh::lean_unbox_uint64(v_a_2487_);
                    leanh::lean_inc(v_reason_2480_);
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
    mut v_reason_2493_: *mut leanh::LeanObject,
    mut v_as_2494_: *mut leanh::LeanObject,
    mut v_sz_2495_: *mut leanh::LeanObject,
    mut v_i_2496_: *mut leanh::LeanObject,
    mut v_b_2497_: *mut leanh::LeanObject,
    mut v___y_2498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2499_: usize = 0;
    let mut v_i_boxed_2500_: usize = 0;
    let mut v_res_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2499_ = leanh::lean_unbox_usize(v_sz_2495_);
    leanh::lean_dec(v_sz_2495_);
    v_i_boxed_2500_ = leanh::lean_unbox_usize(v_i_2496_);
    leanh::lean_dec(v_i_2496_);
    v_res_2501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(v_reason_2493_, v_as_2494_, v_sz_boxed_2499_, v_i_boxed_2500_, v_b_2497_);
    leanh::lean_dec_ref(v_as_2494_);
    return v_res_2501_;
}
pub unsafe fn l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren___boxed(
    mut v_state_2502_: *mut leanh::LeanObject,
    mut v_id_2503_: *mut leanh::LeanObject,
    mut v_reason_2504_: *mut leanh::LeanObject,
    mut v_a_2505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_boxed_2506_: u64 = 0;
    let mut v_res_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_id_boxed_2506_ = leanh::lean_unbox_uint64(v_id_2503_);
    leanh::lean_dec_ref(v_id_2503_);
    v_res_2507_ =
        l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(
            v_state_2502_,
            v_id_boxed_2506_,
            v_reason_2504_,
        );
    return v_res_2507_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(
    mut v_00_u03b4_2508_: *mut leanh::LeanObject,
    mut v_t_2509_: *mut leanh::LeanObject,
    mut v_k_2510_: u64,
) -> *mut leanh::LeanObject {
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2511_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_t_2509_, v_k_2510_);
    return v___x_2511_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___boxed(
    mut v_00_u03b4_2512_: *mut leanh::LeanObject,
    mut v_t_2513_: *mut leanh::LeanObject,
    mut v_k_2514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_boxed_2515_: u64 = 0;
    let mut v_res_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_2515_ = leanh::lean_unbox_uint64(v_k_2514_);
    leanh::lean_dec_ref(v_k_2514_);
    v_res_2516_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(v_00_u03b4_2512_, v_t_2513_, v_k_boxed_2515_);
    leanh::lean_dec(v_t_2513_);
    return v_res_2516_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(
    mut v_00_u03b2_2517_: *mut leanh::LeanObject,
    mut v_k_2518_: u64,
    mut v_t_2519_: *mut leanh::LeanObject,
    mut v_h_2520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2521_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_2518_, v_t_2519_);
    return v___x_2521_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___boxed(
    mut v_00_u03b2_2522_: *mut leanh::LeanObject,
    mut v_k_2523_: *mut leanh::LeanObject,
    mut v_t_2524_: *mut leanh::LeanObject,
    mut v_h_2525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_boxed_2526_: u64 = 0;
    let mut v_res_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_2526_ = leanh::lean_unbox_uint64(v_k_2523_);
    leanh::lean_dec_ref(v_k_2523_);
    v_res_2527_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(v_00_u03b2_2522_, v_k_boxed_2526_, v_t_2524_, v_h_2525_);
    return v_res_2527_;
}
pub unsafe fn l_Std_CancellationContext_cancel___lam__0(
    mut v_id_2528_: u64,
    mut v_reason_2529_: *mut leanh::LeanObject,
    mut v___y_2530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_id_2535_: *mut leanh::LeanObject,
    mut v_reason_2536_: *mut leanh::LeanObject,
    mut v___y_2537_: *mut leanh::LeanObject,
    mut v___y_2538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_boxed_2539_: u64 = 0;
    let mut v_res_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_id_boxed_2539_ = leanh::lean_unbox_uint64(v_id_2535_);
    leanh::lean_dec_ref(v_id_2535_);
    v_res_2540_ =
        l_Std_CancellationContext_cancel___lam__0(v_id_boxed_2539_, v_reason_2536_, v___y_2537_);
    leanh::lean_dec(v___y_2537_);
    return v_res_2540_;
}
pub unsafe fn l_Std_CancellationContext_cancel(
    mut v_x_2541_: *mut leanh::LeanObject,
    mut v_reason_2542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_state_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_token_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_2546_: u64 = 0;
    let mut v___x_2547_: u8 = 0;
    v_state_2544_ = leanh::lean_ctor_get(v_x_2541_, 0);
    leanh::lean_inc_ref(v_state_2544_);
    v_token_2545_ = leanh::lean_ctor_get(v_x_2541_, 1);
    leanh::lean_inc_ref(v_token_2545_);
    v_id_2546_ = leanh::lean_ctor_get_uint64(
        v_x_2541_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    leanh::lean_dec_ref(v_x_2541_);
    v___x_2547_ = l_Std_CancellationToken_isCancelled(v_token_2545_);
    if v___x_2547_ == 0 {
        let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2548_ = leanh::lean_box_uint64(v_id_2546_);
        v___f_2549_ = leanh::lean_alloc_closure(
            l_Std_CancellationContext_cancel___lam__0___boxed as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_2549_, 0, v___x_2548_);
        leanh::lean_closure_set(v___f_2549_, 1, v_reason_2542_);
        v___x_2550_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(
            v_state_2544_,
            v___f_2549_,
        );
        return v___x_2550_;
    } else {
        let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_state_2544_);
        leanh::lean_dec(v_reason_2542_);
        v___x_2551_ = leanh::lean_box(0);
        return v___x_2551_;
    }
}
pub unsafe fn l_Std_CancellationContext_cancel___boxed(
    mut v_x_2552_: *mut leanh::LeanObject,
    mut v_reason_2553_: *mut leanh::LeanObject,
    mut v_a_2554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2555_ = l_Std_CancellationContext_cancel(v_x_2552_, v_reason_2553_);
    return v_res_2555_;
}
pub unsafe fn l_Std_CancellationContext_isCancelled(
    mut v_x_2556_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_token_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: u8 = 0;
    v_token_2558_ = leanh::lean_ctor_get(v_x_2556_, 1);
    leanh::lean_inc_ref(v_token_2558_);
    leanh::lean_dec_ref(v_x_2556_);
    v___x_2559_ = l_Std_CancellationToken_isCancelled(v_token_2558_);
    return v___x_2559_;
}
pub unsafe fn l_Std_CancellationContext_isCancelled___boxed(
    mut v_x_2560_: *mut leanh::LeanObject,
    mut v_a_2561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2562_: u8 = 0;
    let mut v_r_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2562_ = l_Std_CancellationContext_isCancelled(v_x_2560_);
    v_r_2563_ = leanh::lean_box((v_res_2562_) as usize);
    return v_r_2563_;
}
pub unsafe fn l_Std_CancellationContext_getCancellationReason(
    mut v_x_2564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_token_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_token_2566_ = leanh::lean_ctor_get(v_x_2564_, 1);
    leanh::lean_inc_ref(v_token_2566_);
    leanh::lean_dec_ref(v_x_2564_);
    v___x_2567_ = l_Std_CancellationToken_getCancellationReason(v_token_2566_);
    return v___x_2567_;
}
pub unsafe fn l_Std_CancellationContext_getCancellationReason___boxed(
    mut v_x_2568_: *mut leanh::LeanObject,
    mut v_a_2569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2570_ = l_Std_CancellationContext_getCancellationReason(v_x_2568_);
    return v_res_2570_;
}
pub unsafe fn l_Std_CancellationContext_done(
    mut v_x_2571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_token_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_token_2573_ = leanh::lean_ctor_get(v_x_2571_, 1);
    leanh::lean_inc_ref(v_token_2573_);
    leanh::lean_dec_ref(v_x_2571_);
    v___x_2574_ = l_Std_CancellationToken_wait(v_token_2573_);
    return v___x_2574_;
}
pub unsafe fn l_Std_CancellationContext_done___boxed(
    mut v_x_2575_: *mut leanh::LeanObject,
    mut v_a_2576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2577_ = l_Std_CancellationContext_done(v_x_2575_);
    return v_res_2577_;
}
pub unsafe fn l_Std_CancellationContext_doneSelector(
    mut v_x_2578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_token_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_token_2579_ = leanh::lean_ctor_get(v_x_2578_, 1);
    leanh::lean_inc_ref(v_token_2579_);
    leanh::lean_dec_ref(v_x_2578_);
    v___x_2580_ = l_Std_CancellationToken_selector(v_token_2579_);
    return v___x_2580_;
}
pub unsafe fn l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(
    mut v_state_2581_: *mut leanh::LeanObject,
    mut v_id_2582_: u64,
) -> *mut leanh::LeanObject {
    let mut v_tokens_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tokens_2583_ = leanh::lean_ctor_get(v_state_2581_, 0);
    v___x_2584_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_tokens_2583_, v_id_2582_);
    if leanh::lean_obj_tag(v___x_2584_) == 0 {
        let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2585_ = leanh::lean_unsigned_to_nat(0);
        return v___x_2585_;
    } else {
        let mut v_val_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2590_: u8 = 0;
        v_val_2586_ = leanh::lean_ctor_get(v___x_2584_, 0);
        leanh::lean_inc(v_val_2586_);
        leanh::lean_dec_ref_known(v___x_2584_, 1);
        v_snd_2587_ = leanh::lean_ctor_get(v_val_2586_, 1);
        leanh::lean_inc(v_snd_2587_);
        leanh::lean_dec(v_val_2586_);
        v___x_2588_ = leanh::lean_unsigned_to_nat(0);
        v___x_2589_ = lean_array_get_size(v_snd_2587_);
        v___x_2590_ = lean_nat_dec_lt(v___x_2588_, v___x_2589_);
        if v___x_2590_ == 0 {
            let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_snd_2587_);
            v___x_2591_ = leanh::lean_unsigned_to_nat(1);
            return v___x_2591_;
        } else {
            let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2593_: u8 = 0;
            v___x_2592_ = leanh::lean_unsigned_to_nat(1);
            v___x_2593_ = lean_nat_dec_le(v___x_2589_, v___x_2589_);
            if v___x_2593_ == 0 {
                if v___x_2590_ == 0 {
                    leanh::lean_dec(v_snd_2587_);
                    return v___x_2592_;
                } else {
                    let mut v___x_2594_: usize = 0;
                    let mut v___x_2595_: usize = 0;
                    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_2594_ = 0usize;
                    v___x_2595_ = lean_usize_of_nat(v___x_2589_);
                    v___x_2596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_2581_, v_snd_2587_, v___x_2594_, v___x_2595_, v___x_2588_);
                    leanh::lean_dec(v_snd_2587_);
                    v___x_2597_ = lean_nat_add(v___x_2592_, v___x_2596_);
                    leanh::lean_dec(v___x_2596_);
                    return v___x_2597_;
                }
            } else {
                let mut v___x_2598_: usize = 0;
                let mut v___x_2599_: usize = 0;
                let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2598_ = 0usize;
                v___x_2599_ = lean_usize_of_nat(v___x_2589_);
                v___x_2600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_2581_, v_snd_2587_, v___x_2598_, v___x_2599_, v___x_2588_);
                leanh::lean_dec(v_snd_2587_);
                v___x_2601_ = lean_nat_add(v___x_2592_, v___x_2600_);
                leanh::lean_dec(v___x_2600_);
                return v___x_2601_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(
    mut v_state_2602_: *mut leanh::LeanObject,
    mut v_as_2603_: *mut leanh::LeanObject,
    mut v_i_2604_: usize,
    mut v_stop_2605_: usize,
    mut v_b_2606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2607_: u8 = 0;
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: u64 = 0;
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: usize = 0;
    let mut v___x_2613_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2607_ = lean_usize_dec_eq(v_i_2604_, v_stop_2605_);
                if v___x_2607_ == 0 {
                    v___x_2608_ = lean_array_uget_borrowed(v_as_2603_, v_i_2604_);
                    v___x_2609_ = leanh::lean_unbox_uint64(v___x_2608_);
                    v___x_2610_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(v_state_2602_, v___x_2609_);
                    v___x_2611_ = lean_nat_add(v_b_2606_, v___x_2610_);
                    leanh::lean_dec(v___x_2610_);
                    leanh::lean_dec(v_b_2606_);
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
    mut v_state_2615_: *mut leanh::LeanObject,
    mut v_as_2616_: *mut leanh::LeanObject,
    mut v_i_2617_: *mut leanh::LeanObject,
    mut v_stop_2618_: *mut leanh::LeanObject,
    mut v_b_2619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2620_: usize = 0;
    let mut v_stop_boxed_2621_: usize = 0;
    let mut v_res_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2620_ = leanh::lean_unbox_usize(v_i_2617_);
    leanh::lean_dec(v_i_2617_);
    v_stop_boxed_2621_ = leanh::lean_unbox_usize(v_stop_2618_);
    leanh::lean_dec(v_stop_2618_);
    v_res_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_2615_, v_as_2616_, v_i_boxed_2620_, v_stop_boxed_2621_, v_b_2619_);
    leanh::lean_dec_ref(v_as_2616_);
    leanh::lean_dec_ref(v_state_2615_);
    return v_res_2622_;
}
pub unsafe fn l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec___boxed(
    mut v_state_2623_: *mut leanh::LeanObject,
    mut v_id_2624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_boxed_2625_: u64 = 0;
    let mut v_res_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_id_boxed_2625_ = leanh::lean_unbox_uint64(v_id_2624_);
    leanh::lean_dec_ref(v_id_2624_);
    v_res_2626_ =
        l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(
            v_state_2623_,
            v_id_boxed_2625_,
        );
    leanh::lean_dec_ref(v_state_2623_);
    return v_res_2626_;
}
pub unsafe fn l_Std_CancellationContext_countAliveTokens___lam__0(
    mut v_id_2627_: u64,
    mut v___y_2628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2630_ = lean_st_ref_get(v___y_2628_);
    v___x_2631_ =
        l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(
            v___x_2630_,
            v_id_2627_,
        );
    leanh::lean_dec(v___x_2630_);
    return v___x_2631_;
}
pub unsafe fn l_Std_CancellationContext_countAliveTokens___lam__0___boxed(
    mut v_id_2632_: *mut leanh::LeanObject,
    mut v___y_2633_: *mut leanh::LeanObject,
    mut v___y_2634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_boxed_2635_: u64 = 0;
    let mut v_res_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_id_boxed_2635_ = leanh::lean_unbox_uint64(v_id_2632_);
    leanh::lean_dec_ref(v_id_2632_);
    v_res_2636_ =
        l_Std_CancellationContext_countAliveTokens___lam__0(v_id_boxed_2635_, v___y_2633_);
    leanh::lean_dec(v___y_2633_);
    return v_res_2636_;
}
pub unsafe fn l_Std_CancellationContext_countAliveTokens(
    mut v_x_2637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_state_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_2640_: u64 = 0;
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_state_2639_ = leanh::lean_ctor_get(v_x_2637_, 0);
    leanh::lean_inc_ref(v_state_2639_);
    v_id_2640_ = leanh::lean_ctor_get_uint64(
        v_x_2637_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    leanh::lean_dec_ref(v_x_2637_);
    v___x_2641_ = leanh::lean_box_uint64(v_id_2640_);
    v___f_2642_ = leanh::lean_alloc_closure(
        l_Std_CancellationContext_countAliveTokens___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2642_, 0, v___x_2641_);
    v___x_2643_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(
        v_state_2639_,
        v___f_2642_,
    );
    return v___x_2643_;
}
pub unsafe fn l_Std_CancellationContext_countAliveTokens___boxed(
    mut v_x_2644_: *mut leanh::LeanObject,
    mut v_a_2645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2646_ = l_Std_CancellationContext_countAliveTokens(v_x_2644_);
    return v_res_2646_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sync_CancellationContext(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sync_CancellationToken(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_UInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_CancellationContext(
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
pub unsafe fn initialize_Std_Sync_CancellationContext(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sync_CancellationToken(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Ord_UInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_CancellationContext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sync_CancellationContext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Sync_CancellationContext(builtin);
}