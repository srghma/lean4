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
pub static l_Std_CancellationContext_new___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Std_CancellationContext_new___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationContext_new___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(
    mut v_k_1324_: u64,
    mut v_v_1325_: *mut crate::leanh::LeanObject,
    mut v_t_1326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1334_: u8 = 0;
    let mut v___x_1335_: u64 = 0;
    let mut v___x_1336_: u8 = 0;
    let mut v___x_1337_: u64 = 0;
    let mut v___x_1338_: u8 = 0;
    let mut v_impl_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: u8 = 0;
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1357_: u8 = 0;
    let mut v_size_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: u8 = 0;
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1394_: u8 = 0;
    let mut v_unused_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1411_: u8 = 0;
    let mut v_unused_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1418_: u8 = 0;
    let mut v_unused_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v_k_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1435_: u8 = 0;
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1446_: u8 = 0;
    let mut v_unused_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1450_: u8 = 0;
    let mut v_unused_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1458_: u8 = 0;
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1466_: u8 = 0;
    let mut v_unused_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: u8 = 0;
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1496_: u8 = 0;
    let mut v_size_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: u8 = 0;
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1508_: u8 = 0;
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1534_: u8 = 0;
    let mut v_unused_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1548_: u8 = 0;
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1552_: u8 = 0;
    let mut v_unused_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1559_: u8 = 0;
    let mut v_unused_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1571_: u8 = 0;
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1579_: u8 = 0;
    let mut v_unused_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1587_: u8 = 0;
    let mut v_k_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1592_: u8 = 0;
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut v_unused_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1607_: u8 = 0;
    let mut v_unused_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1615_: u8 = 0;
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1326_) == 0 {
                    v_size_1327_ = crate::leanh::lean_ctor_get(v_t_1326_, 0);
                    v_k_1328_ = crate::leanh::lean_ctor_get(v_t_1326_, 1);
                    v_v_1329_ = crate::leanh::lean_ctor_get(v_t_1326_, 2);
                    v_l_1330_ = crate::leanh::lean_ctor_get(v_t_1326_, 3);
                    v_r_1331_ = crate::leanh::lean_ctor_get(v_t_1326_, 4);
                    v_isSharedCheck_1615_ = (!crate::leanh::lean_is_exclusive(v_t_1326_)) as u8;
                    if v_isSharedCheck_1615_ == 0 {
                        v___x_1333_ = v_t_1326_;
                        v_isShared_1334_ = v_isSharedCheck_1615_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1331_);
                        crate::leanh::lean_inc(v_l_1330_);
                        crate::leanh::lean_inc(v_v_1329_);
                        crate::leanh::lean_inc(v_k_1328_);
                        crate::leanh::lean_inc(v_size_1327_);
                        crate::leanh::lean_dec(v_t_1326_);
                        v___x_1333_ = crate::leanh::lean_box(0);
                        v_isShared_1334_ = v_isSharedCheck_1615_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1616_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1617_ = crate::leanh::lean_box_uint64(v_k_1324_);
                    v___x_1618_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1618_, 0, v___x_1616_);
                    crate::leanh::lean_ctor_set(v___x_1618_, 1, v___x_1617_);
                    crate::leanh::lean_ctor_set(v___x_1618_, 2, v_v_1325_);
                    crate::leanh::lean_ctor_set(v___x_1618_, 3, v_t_1326_);
                    crate::leanh::lean_ctor_set(v___x_1618_, 4, v_t_1326_);
                    return v___x_1618_;
                }
            }
            1 => {
                v___x_1335_ = crate::leanh::lean_unbox_uint64(v_k_1328_);
                v___x_1336_ = lean_uint64_dec_lt(v_k_1324_, v___x_1335_);
                if v___x_1336_ == 0 {
                    v___x_1337_ = crate::leanh::lean_unbox_uint64(v_k_1328_);
                    v___x_1338_ = lean_uint64_dec_eq(v_k_1324_, v___x_1337_);
                    if v___x_1338_ == 0 {
                        crate::leanh::lean_dec(v_size_1327_);
                        v_impl_1339_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_k_1324_, v_v_1325_, v_r_1331_);
                        v___x_1340_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_1330_) == 0 {
                            v_size_1341_ = crate::leanh::lean_ctor_get(v_l_1330_, 0);
                            v_size_1342_ = crate::leanh::lean_ctor_get(v_impl_1339_, 0);
                            crate::leanh::lean_inc(v_size_1342_);
                            v_k_1343_ = crate::leanh::lean_ctor_get(v_impl_1339_, 1);
                            crate::leanh::lean_inc(v_k_1343_);
                            v_v_1344_ = crate::leanh::lean_ctor_get(v_impl_1339_, 2);
                            crate::leanh::lean_inc(v_v_1344_);
                            v_l_1345_ = crate::leanh::lean_ctor_get(v_impl_1339_, 3);
                            crate::leanh::lean_inc(v_l_1345_);
                            v_r_1346_ = crate::leanh::lean_ctor_get(v_impl_1339_, 4);
                            crate::leanh::lean_inc(v_r_1346_);
                            v___x_1347_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1348_ = lean_nat_mul(v___x_1347_, v_size_1341_);
                            v___x_1349_ = lean_nat_dec_lt(v___x_1348_, v_size_1342_);
                            crate::leanh::lean_dec(v___x_1348_);
                            if v___x_1349_ == 0 {
                                crate::leanh::lean_dec(v_r_1346_);
                                crate::leanh::lean_dec(v_l_1345_);
                                crate::leanh::lean_dec(v_v_1344_);
                                crate::leanh::lean_dec(v_k_1343_);
                                v___x_1350_ = lean_nat_add(v___x_1340_, v_size_1341_);
                                v___x_1351_ = lean_nat_add(v___x_1350_, v_size_1342_);
                                crate::leanh::lean_dec(v_size_1342_);
                                crate::leanh::lean_dec(v___x_1350_);
                                if v_isShared_1334_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1333_, 4, v_impl_1339_);
                                    crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1351_);
                                    v___x_1353_ = v___x_1333_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1354_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1354_,
                                        0,
                                        v___x_1351_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1354_,
                                        1,
                                        v_k_1328_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1354_,
                                        2,
                                        v_v_1329_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1354_,
                                        3,
                                        v_l_1330_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                                    (!crate::leanh::lean_is_exclusive(v_impl_1339_)) as u8;
                                if v_isSharedCheck_1418_ == 0 {
                                    v_unused_1419_ = crate::leanh::lean_ctor_get(v_impl_1339_, 4);
                                    crate::leanh::lean_dec(v_unused_1419_);
                                    v_unused_1420_ = crate::leanh::lean_ctor_get(v_impl_1339_, 3);
                                    crate::leanh::lean_dec(v_unused_1420_);
                                    v_unused_1421_ = crate::leanh::lean_ctor_get(v_impl_1339_, 2);
                                    crate::leanh::lean_dec(v_unused_1421_);
                                    v_unused_1422_ = crate::leanh::lean_ctor_get(v_impl_1339_, 1);
                                    crate::leanh::lean_dec(v_unused_1422_);
                                    v_unused_1423_ = crate::leanh::lean_ctor_get(v_impl_1339_, 0);
                                    crate::leanh::lean_dec(v_unused_1423_);
                                    v___x_1356_ = v_impl_1339_;
                                    v_isShared_1357_ = v_isSharedCheck_1418_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_1339_);
                                    v___x_1356_ = crate::leanh::lean_box(0);
                                    v_isShared_1357_ = v_isSharedCheck_1418_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1424_ = crate::leanh::lean_ctor_get(v_impl_1339_, 3);
                            crate::leanh::lean_inc(v_l_1424_);
                            if crate::leanh::lean_obj_tag(v_l_1424_) == 0 {
                                v_r_1425_ = crate::leanh::lean_ctor_get(v_impl_1339_, 4);
                                v_k_1426_ = crate::leanh::lean_ctor_get(v_impl_1339_, 1);
                                v_v_1427_ = crate::leanh::lean_ctor_get(v_impl_1339_, 2);
                                v_isSharedCheck_1450_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1339_)) as u8;
                                if v_isSharedCheck_1450_ == 0 {
                                    v_unused_1451_ = crate::leanh::lean_ctor_get(v_impl_1339_, 3);
                                    crate::leanh::lean_dec(v_unused_1451_);
                                    v_unused_1452_ = crate::leanh::lean_ctor_get(v_impl_1339_, 0);
                                    crate::leanh::lean_dec(v_unused_1452_);
                                    v___x_1429_ = v_impl_1339_;
                                    v_isShared_1430_ = v_isSharedCheck_1450_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_1425_);
                                    crate::leanh::lean_inc(v_v_1427_);
                                    crate::leanh::lean_inc(v_k_1426_);
                                    crate::leanh::lean_dec(v_impl_1339_);
                                    v___x_1429_ = crate::leanh::lean_box(0);
                                    v_isShared_1430_ = v_isSharedCheck_1450_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1453_ = crate::leanh::lean_ctor_get(v_impl_1339_, 4);
                                crate::leanh::lean_inc(v_r_1453_);
                                if crate::leanh::lean_obj_tag(v_r_1453_) == 0 {
                                    v_k_1454_ = crate::leanh::lean_ctor_get(v_impl_1339_, 1);
                                    v_v_1455_ = crate::leanh::lean_ctor_get(v_impl_1339_, 2);
                                    v_isSharedCheck_1466_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_1339_)) as u8;
                                    if v_isSharedCheck_1466_ == 0 {
                                        v_unused_1467_ =
                                            crate::leanh::lean_ctor_get(v_impl_1339_, 4);
                                        crate::leanh::lean_dec(v_unused_1467_);
                                        v_unused_1468_ =
                                            crate::leanh::lean_ctor_get(v_impl_1339_, 3);
                                        crate::leanh::lean_dec(v_unused_1468_);
                                        v_unused_1469_ =
                                            crate::leanh::lean_ctor_get(v_impl_1339_, 0);
                                        crate::leanh::lean_dec(v_unused_1469_);
                                        v___x_1457_ = v_impl_1339_;
                                        v_isShared_1458_ = v_isSharedCheck_1466_;
                                        state = 18;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_1455_);
                                        crate::leanh::lean_inc(v_k_1454_);
                                        crate::leanh::lean_dec(v_impl_1339_);
                                        v___x_1457_ = crate::leanh::lean_box(0);
                                        v_isShared_1458_ = v_isSharedCheck_1466_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_1470_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1334_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1333_, 4, v_impl_1339_);
                                        crate::leanh::lean_ctor_set(v___x_1333_, 3, v_r_1453_);
                                        crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1470_);
                                        v___x_1472_ = v___x_1333_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1473_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1473_,
                                            0,
                                            v___x_1470_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1473_,
                                            1,
                                            v_k_1328_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1473_,
                                            2,
                                            v_v_1329_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1473_,
                                            3,
                                            v_r_1453_,
                                        );
                                        crate::leanh::lean_ctor_set(
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
                        crate::leanh::lean_dec(v_v_1329_);
                        crate::leanh::lean_dec(v_k_1328_);
                        v___x_1474_ = crate::leanh::lean_box_uint64(v_k_1324_);
                        if v_isShared_1334_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1333_, 2, v_v_1325_);
                            crate::leanh::lean_ctor_set(v___x_1333_, 1, v___x_1474_);
                            v___x_1476_ = v___x_1333_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1477_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_size_1327_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1477_, 1, v___x_1474_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_v_1325_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1477_, 3, v_l_1330_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1477_, 4, v_r_1331_);
                            v___x_1476_ = v_reuseFailAlloc_1477_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_size_1327_);
                    v_impl_1478_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_k_1324_, v_v_1325_, v_l_1330_);
                    v___x_1479_ = crate::leanh::lean_unsigned_to_nat(1);
                    if crate::leanh::lean_obj_tag(v_r_1331_) == 0 {
                        v_size_1480_ = crate::leanh::lean_ctor_get(v_r_1331_, 0);
                        v_size_1481_ = crate::leanh::lean_ctor_get(v_impl_1478_, 0);
                        crate::leanh::lean_inc(v_size_1481_);
                        v_k_1482_ = crate::leanh::lean_ctor_get(v_impl_1478_, 1);
                        crate::leanh::lean_inc(v_k_1482_);
                        v_v_1483_ = crate::leanh::lean_ctor_get(v_impl_1478_, 2);
                        crate::leanh::lean_inc(v_v_1483_);
                        v_l_1484_ = crate::leanh::lean_ctor_get(v_impl_1478_, 3);
                        crate::leanh::lean_inc(v_l_1484_);
                        v_r_1485_ = crate::leanh::lean_ctor_get(v_impl_1478_, 4);
                        crate::leanh::lean_inc(v_r_1485_);
                        v___x_1486_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_1487_ = lean_nat_mul(v___x_1486_, v_size_1480_);
                        v___x_1488_ = lean_nat_dec_lt(v___x_1487_, v_size_1481_);
                        crate::leanh::lean_dec(v___x_1487_);
                        if v___x_1488_ == 0 {
                            crate::leanh::lean_dec(v_r_1485_);
                            crate::leanh::lean_dec(v_l_1484_);
                            crate::leanh::lean_dec(v_v_1483_);
                            crate::leanh::lean_dec(v_k_1482_);
                            v___x_1489_ = lean_nat_add(v___x_1479_, v_size_1481_);
                            crate::leanh::lean_dec(v_size_1481_);
                            v___x_1490_ = lean_nat_add(v___x_1489_, v_size_1480_);
                            crate::leanh::lean_dec(v___x_1489_);
                            if v_isShared_1334_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1333_, 3, v_impl_1478_);
                                crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1490_);
                                v___x_1492_ = v___x_1333_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_1493_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_k_1328_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 2, v_v_1329_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1493_,
                                    3,
                                    v_impl_1478_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 4, v_r_1331_);
                                v___x_1492_ = v_reuseFailAlloc_1493_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_1559_ =
                                (!crate::leanh::lean_is_exclusive(v_impl_1478_)) as u8;
                            if v_isSharedCheck_1559_ == 0 {
                                v_unused_1560_ = crate::leanh::lean_ctor_get(v_impl_1478_, 4);
                                crate::leanh::lean_dec(v_unused_1560_);
                                v_unused_1561_ = crate::leanh::lean_ctor_get(v_impl_1478_, 3);
                                crate::leanh::lean_dec(v_unused_1561_);
                                v_unused_1562_ = crate::leanh::lean_ctor_get(v_impl_1478_, 2);
                                crate::leanh::lean_dec(v_unused_1562_);
                                v_unused_1563_ = crate::leanh::lean_ctor_get(v_impl_1478_, 1);
                                crate::leanh::lean_dec(v_unused_1563_);
                                v_unused_1564_ = crate::leanh::lean_ctor_get(v_impl_1478_, 0);
                                crate::leanh::lean_dec(v_unused_1564_);
                                v___x_1495_ = v_impl_1478_;
                                v_isShared_1496_ = v_isSharedCheck_1559_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_impl_1478_);
                                v___x_1495_ = crate::leanh::lean_box(0);
                                v_isShared_1496_ = v_isSharedCheck_1559_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_1565_ = crate::leanh::lean_ctor_get(v_impl_1478_, 3);
                        crate::leanh::lean_inc(v_l_1565_);
                        if crate::leanh::lean_obj_tag(v_l_1565_) == 0 {
                            v_r_1566_ = crate::leanh::lean_ctor_get(v_impl_1478_, 4);
                            v_k_1567_ = crate::leanh::lean_ctor_get(v_impl_1478_, 1);
                            v_v_1568_ = crate::leanh::lean_ctor_get(v_impl_1478_, 2);
                            v_isSharedCheck_1579_ =
                                (!crate::leanh::lean_is_exclusive(v_impl_1478_)) as u8;
                            if v_isSharedCheck_1579_ == 0 {
                                v_unused_1580_ = crate::leanh::lean_ctor_get(v_impl_1478_, 3);
                                crate::leanh::lean_dec(v_unused_1580_);
                                v_unused_1581_ = crate::leanh::lean_ctor_get(v_impl_1478_, 0);
                                crate::leanh::lean_dec(v_unused_1581_);
                                v___x_1570_ = v_impl_1478_;
                                v_isShared_1571_ = v_isSharedCheck_1579_;
                                state = 34;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_r_1566_);
                                crate::leanh::lean_inc(v_v_1568_);
                                crate::leanh::lean_inc(v_k_1567_);
                                crate::leanh::lean_dec(v_impl_1478_);
                                v___x_1570_ = crate::leanh::lean_box(0);
                                v_isShared_1571_ = v_isSharedCheck_1579_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_1582_ = crate::leanh::lean_ctor_get(v_impl_1478_, 4);
                            crate::leanh::lean_inc(v_r_1582_);
                            if crate::leanh::lean_obj_tag(v_r_1582_) == 0 {
                                v_k_1583_ = crate::leanh::lean_ctor_get(v_impl_1478_, 1);
                                v_v_1584_ = crate::leanh::lean_ctor_get(v_impl_1478_, 2);
                                v_isSharedCheck_1607_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1478_)) as u8;
                                if v_isSharedCheck_1607_ == 0 {
                                    v_unused_1608_ = crate::leanh::lean_ctor_get(v_impl_1478_, 4);
                                    crate::leanh::lean_dec(v_unused_1608_);
                                    v_unused_1609_ = crate::leanh::lean_ctor_get(v_impl_1478_, 3);
                                    crate::leanh::lean_dec(v_unused_1609_);
                                    v_unused_1610_ = crate::leanh::lean_ctor_get(v_impl_1478_, 0);
                                    crate::leanh::lean_dec(v_unused_1610_);
                                    v___x_1586_ = v_impl_1478_;
                                    v_isShared_1587_ = v_isSharedCheck_1607_;
                                    state = 37;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_v_1584_);
                                    crate::leanh::lean_inc(v_k_1583_);
                                    crate::leanh::lean_dec(v_impl_1478_);
                                    v___x_1586_ = crate::leanh::lean_box(0);
                                    v_isShared_1587_ = v_isSharedCheck_1607_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_1611_ = crate::leanh::lean_unsigned_to_nat(2);
                                if v_isShared_1334_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1333_, 4, v_r_1582_);
                                    crate::leanh::lean_ctor_set(v___x_1333_, 3, v_impl_1478_);
                                    crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1611_);
                                    v___x_1613_ = v___x_1333_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1614_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1614_,
                                        0,
                                        v___x_1611_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1614_,
                                        1,
                                        v_k_1328_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1614_,
                                        2,
                                        v_v_1329_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1614_,
                                        3,
                                        v_impl_1478_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                v_size_1358_ = crate::leanh::lean_ctor_get(v_l_1345_, 0);
                v_k_1359_ = crate::leanh::lean_ctor_get(v_l_1345_, 1);
                v_v_1360_ = crate::leanh::lean_ctor_get(v_l_1345_, 2);
                v_l_1361_ = crate::leanh::lean_ctor_get(v_l_1345_, 3);
                v_r_1362_ = crate::leanh::lean_ctor_get(v_l_1345_, 4);
                v_size_1363_ = crate::leanh::lean_ctor_get(v_r_1346_, 0);
                v___x_1364_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1365_ = lean_nat_mul(v___x_1364_, v_size_1363_);
                v___x_1366_ = lean_nat_dec_lt(v_size_1358_, v___x_1365_);
                crate::leanh::lean_dec(v___x_1365_);
                if v___x_1366_ == 0 {
                    crate::leanh::lean_inc(v_r_1362_);
                    crate::leanh::lean_inc(v_l_1361_);
                    crate::leanh::lean_inc(v_v_1360_);
                    crate::leanh::lean_inc(v_k_1359_);
                    v_isSharedCheck_1394_ = (!crate::leanh::lean_is_exclusive(v_l_1345_)) as u8;
                    if v_isSharedCheck_1394_ == 0 {
                        v_unused_1395_ = crate::leanh::lean_ctor_get(v_l_1345_, 4);
                        crate::leanh::lean_dec(v_unused_1395_);
                        v_unused_1396_ = crate::leanh::lean_ctor_get(v_l_1345_, 3);
                        crate::leanh::lean_dec(v_unused_1396_);
                        v_unused_1397_ = crate::leanh::lean_ctor_get(v_l_1345_, 2);
                        crate::leanh::lean_dec(v_unused_1397_);
                        v_unused_1398_ = crate::leanh::lean_ctor_get(v_l_1345_, 1);
                        crate::leanh::lean_dec(v_unused_1398_);
                        v_unused_1399_ = crate::leanh::lean_ctor_get(v_l_1345_, 0);
                        crate::leanh::lean_dec(v_unused_1399_);
                        v___x_1368_ = v_l_1345_;
                        v_isShared_1369_ = v_isSharedCheck_1394_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_1345_);
                        v___x_1368_ = crate::leanh::lean_box(0);
                        v_isShared_1369_ = v_isSharedCheck_1394_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1333_);
                    v___x_1400_ = lean_nat_add(v___x_1340_, v_size_1341_);
                    v___x_1401_ = lean_nat_add(v___x_1400_, v_size_1342_);
                    crate::leanh::lean_dec(v_size_1342_);
                    v___x_1402_ = lean_nat_add(v___x_1400_, v_size_1358_);
                    crate::leanh::lean_dec(v___x_1400_);
                    crate::leanh::lean_inc_ref(v_l_1330_);
                    if v_isShared_1357_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1356_, 4, v_l_1345_);
                        crate::leanh::lean_ctor_set(v___x_1356_, 3, v_l_1330_);
                        crate::leanh::lean_ctor_set(v___x_1356_, 2, v_v_1329_);
                        crate::leanh::lean_ctor_set(v___x_1356_, 1, v_k_1328_);
                        crate::leanh::lean_ctor_set(v___x_1356_, 0, v___x_1402_);
                        v___x_1404_ = v___x_1356_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1417_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1402_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1328_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1329_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_l_1330_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 4, v_l_1345_);
                        v___x_1404_ = v_reuseFailAlloc_1417_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1370_ = lean_nat_add(v___x_1340_, v_size_1341_);
                v___x_1371_ = lean_nat_add(v___x_1370_, v_size_1342_);
                crate::leanh::lean_dec(v_size_1342_);
                if crate::leanh::lean_obj_tag(v_l_1361_) == 0 {
                    v_size_1392_ = crate::leanh::lean_ctor_get(v_l_1361_, 0);
                    crate::leanh::lean_inc(v_size_1392_);
                    v___y_1384_ = v_size_1392_;
                    state = 8;
                    continue;
                } else {
                    v___x_1393_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1384_ = v___x_1393_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1376_ = lean_nat_add(v___y_1373_, v___y_1375_);
                crate::leanh::lean_dec(v___y_1375_);
                crate::leanh::lean_dec(v___y_1373_);
                if v_isShared_1369_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1368_, 4, v_r_1346_);
                    crate::leanh::lean_ctor_set(v___x_1368_, 3, v_r_1362_);
                    crate::leanh::lean_ctor_set(v___x_1368_, 2, v_v_1344_);
                    crate::leanh::lean_ctor_set(v___x_1368_, 1, v_k_1343_);
                    crate::leanh::lean_ctor_set(v___x_1368_, 0, v___x_1376_);
                    v___x_1378_ = v___x_1368_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1382_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1376_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_k_1343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1382_, 2, v_v_1344_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1382_, 3, v_r_1362_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1382_, 4, v_r_1346_);
                    v___x_1378_ = v_reuseFailAlloc_1382_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1357_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1356_, 4, v___x_1378_);
                    crate::leanh::lean_ctor_set(v___x_1356_, 3, v___y_1374_);
                    crate::leanh::lean_ctor_set(v___x_1356_, 2, v_v_1360_);
                    crate::leanh::lean_ctor_set(v___x_1356_, 1, v_k_1359_);
                    crate::leanh::lean_ctor_set(v___x_1356_, 0, v___x_1371_);
                    v___x_1380_ = v___x_1356_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1381_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1371_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_k_1359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1381_, 2, v_v_1360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1381_, 3, v___y_1374_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1381_, 4, v___x_1378_);
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
                crate::leanh::lean_dec(v___y_1384_);
                crate::leanh::lean_dec(v___x_1370_);
                if v_isShared_1334_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1333_, 4, v_l_1361_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1385_);
                    v___x_1387_ = v___x_1333_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1391_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_k_1328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_v_1329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_l_1330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 4, v_l_1361_);
                    v___x_1387_ = v_reuseFailAlloc_1391_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1388_ = lean_nat_add(v___x_1340_, v_size_1363_);
                if crate::leanh::lean_obj_tag(v_r_1362_) == 0 {
                    v_size_1389_ = crate::leanh::lean_ctor_get(v_r_1362_, 0);
                    crate::leanh::lean_inc(v_size_1389_);
                    v___y_1373_ = v___x_1388_;
                    v___y_1374_ = v___x_1387_;
                    v___y_1375_ = v_size_1389_;
                    state = 5;
                    continue;
                } else {
                    v___x_1390_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1373_ = v___x_1388_;
                    v___y_1374_ = v___x_1387_;
                    v___y_1375_ = v___x_1390_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1411_ = (!crate::leanh::lean_is_exclusive(v_l_1330_)) as u8;
                if v_isSharedCheck_1411_ == 0 {
                    v_unused_1412_ = crate::leanh::lean_ctor_get(v_l_1330_, 4);
                    crate::leanh::lean_dec(v_unused_1412_);
                    v_unused_1413_ = crate::leanh::lean_ctor_get(v_l_1330_, 3);
                    crate::leanh::lean_dec(v_unused_1413_);
                    v_unused_1414_ = crate::leanh::lean_ctor_get(v_l_1330_, 2);
                    crate::leanh::lean_dec(v_unused_1414_);
                    v_unused_1415_ = crate::leanh::lean_ctor_get(v_l_1330_, 1);
                    crate::leanh::lean_dec(v_unused_1415_);
                    v_unused_1416_ = crate::leanh::lean_ctor_get(v_l_1330_, 0);
                    crate::leanh::lean_dec(v_unused_1416_);
                    v___x_1406_ = v_l_1330_;
                    v_isShared_1407_ = v_isSharedCheck_1411_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_1330_);
                    v___x_1406_ = crate::leanh::lean_box(0);
                    v_isShared_1407_ = v_isSharedCheck_1411_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1407_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1406_, 4, v_r_1346_);
                    crate::leanh::lean_ctor_set(v___x_1406_, 3, v___x_1404_);
                    crate::leanh::lean_ctor_set(v___x_1406_, 2, v_v_1344_);
                    crate::leanh::lean_ctor_set(v___x_1406_, 1, v_k_1343_);
                    crate::leanh::lean_ctor_set(v___x_1406_, 0, v___x_1401_);
                    v___x_1409_ = v___x_1406_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1410_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1401_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_k_1343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_v_1344_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 3, v___x_1404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_r_1346_);
                    v___x_1409_ = v_reuseFailAlloc_1410_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1409_;
            }
            13 => {
                v_k_1431_ = crate::leanh::lean_ctor_get(v_l_1424_, 1);
                v_v_1432_ = crate::leanh::lean_ctor_get(v_l_1424_, 2);
                v_isSharedCheck_1446_ = (!crate::leanh::lean_is_exclusive(v_l_1424_)) as u8;
                if v_isSharedCheck_1446_ == 0 {
                    v_unused_1447_ = crate::leanh::lean_ctor_get(v_l_1424_, 4);
                    crate::leanh::lean_dec(v_unused_1447_);
                    v_unused_1448_ = crate::leanh::lean_ctor_get(v_l_1424_, 3);
                    crate::leanh::lean_dec(v_unused_1448_);
                    v_unused_1449_ = crate::leanh::lean_ctor_get(v_l_1424_, 0);
                    crate::leanh::lean_dec(v_unused_1449_);
                    v___x_1434_ = v_l_1424_;
                    v_isShared_1435_ = v_isSharedCheck_1446_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1432_);
                    crate::leanh::lean_inc(v_k_1431_);
                    crate::leanh::lean_dec(v_l_1424_);
                    v___x_1434_ = crate::leanh::lean_box(0);
                    v_isShared_1435_ = v_isSharedCheck_1446_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_1436_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_1425_, 2);
                if v_isShared_1435_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1434_, 4, v_r_1425_);
                    crate::leanh::lean_ctor_set(v___x_1434_, 3, v_r_1425_);
                    crate::leanh::lean_ctor_set(v___x_1434_, 2, v_v_1329_);
                    crate::leanh::lean_ctor_set(v___x_1434_, 1, v_k_1328_);
                    crate::leanh::lean_ctor_set(v___x_1434_, 0, v___x_1340_);
                    v___x_1438_ = v___x_1434_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1445_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_k_1328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_v_1329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 3, v_r_1425_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 4, v_r_1425_);
                    v___x_1438_ = v_reuseFailAlloc_1445_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                crate::leanh::lean_inc(v_r_1425_);
                if v_isShared_1430_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1429_, 3, v_r_1425_);
                    crate::leanh::lean_ctor_set(v___x_1429_, 0, v___x_1340_);
                    v___x_1440_ = v___x_1429_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1444_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_k_1426_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_v_1427_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 3, v_r_1425_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 4, v_r_1425_);
                    v___x_1440_ = v_reuseFailAlloc_1444_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_1334_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1333_, 4, v___x_1440_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 3, v___x_1438_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 2, v_v_1432_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 1, v_k_1431_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1436_);
                    v___x_1442_ = v___x_1333_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1443_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_k_1431_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_v_1432_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 3, v___x_1438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1443_, 4, v___x_1440_);
                    v___x_1442_ = v_reuseFailAlloc_1443_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1442_;
            }
            18 => {
                v___x_1459_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_1458_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1457_, 4, v_l_1424_);
                    crate::leanh::lean_ctor_set(v___x_1457_, 2, v_v_1329_);
                    crate::leanh::lean_ctor_set(v___x_1457_, 1, v_k_1328_);
                    crate::leanh::lean_ctor_set(v___x_1457_, 0, v___x_1340_);
                    v___x_1461_ = v___x_1457_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1465_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_k_1328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_v_1329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 3, v_l_1424_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 4, v_l_1424_);
                    v___x_1461_ = v_reuseFailAlloc_1465_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1334_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1333_, 4, v_r_1453_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 3, v___x_1461_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 2, v_v_1455_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 1, v_k_1454_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1459_);
                    v___x_1463_ = v___x_1333_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1464_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_k_1454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_v_1455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 3, v___x_1461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 4, v_r_1453_);
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
                v_size_1497_ = crate::leanh::lean_ctor_get(v_l_1484_, 0);
                v_size_1498_ = crate::leanh::lean_ctor_get(v_r_1485_, 0);
                v_k_1499_ = crate::leanh::lean_ctor_get(v_r_1485_, 1);
                v_v_1500_ = crate::leanh::lean_ctor_get(v_r_1485_, 2);
                v_l_1501_ = crate::leanh::lean_ctor_get(v_r_1485_, 3);
                v_r_1502_ = crate::leanh::lean_ctor_get(v_r_1485_, 4);
                v___x_1503_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1504_ = lean_nat_mul(v___x_1503_, v_size_1497_);
                v___x_1505_ = lean_nat_dec_lt(v_size_1498_, v___x_1504_);
                crate::leanh::lean_dec(v___x_1504_);
                if v___x_1505_ == 0 {
                    crate::leanh::lean_inc(v_r_1502_);
                    crate::leanh::lean_inc(v_l_1501_);
                    crate::leanh::lean_inc(v_v_1500_);
                    crate::leanh::lean_inc(v_k_1499_);
                    v_isSharedCheck_1534_ = (!crate::leanh::lean_is_exclusive(v_r_1485_)) as u8;
                    if v_isSharedCheck_1534_ == 0 {
                        v_unused_1535_ = crate::leanh::lean_ctor_get(v_r_1485_, 4);
                        crate::leanh::lean_dec(v_unused_1535_);
                        v_unused_1536_ = crate::leanh::lean_ctor_get(v_r_1485_, 3);
                        crate::leanh::lean_dec(v_unused_1536_);
                        v_unused_1537_ = crate::leanh::lean_ctor_get(v_r_1485_, 2);
                        crate::leanh::lean_dec(v_unused_1537_);
                        v_unused_1538_ = crate::leanh::lean_ctor_get(v_r_1485_, 1);
                        crate::leanh::lean_dec(v_unused_1538_);
                        v_unused_1539_ = crate::leanh::lean_ctor_get(v_r_1485_, 0);
                        crate::leanh::lean_dec(v_unused_1539_);
                        v___x_1507_ = v_r_1485_;
                        v_isShared_1508_ = v_isSharedCheck_1534_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_1485_);
                        v___x_1507_ = crate::leanh::lean_box(0);
                        v_isShared_1508_ = v_isSharedCheck_1534_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1333_);
                    v___x_1540_ = lean_nat_add(v___x_1479_, v_size_1481_);
                    crate::leanh::lean_dec(v_size_1481_);
                    v___x_1541_ = lean_nat_add(v___x_1540_, v_size_1480_);
                    crate::leanh::lean_dec(v___x_1540_);
                    v___x_1542_ = lean_nat_add(v___x_1479_, v_size_1480_);
                    v___x_1543_ = lean_nat_add(v___x_1542_, v_size_1498_);
                    crate::leanh::lean_dec(v___x_1542_);
                    crate::leanh::lean_inc_ref(v_r_1331_);
                    if v_isShared_1496_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1495_, 4, v_r_1331_);
                        crate::leanh::lean_ctor_set(v___x_1495_, 3, v_r_1485_);
                        crate::leanh::lean_ctor_set(v___x_1495_, 2, v_v_1329_);
                        crate::leanh::lean_ctor_set(v___x_1495_, 1, v_k_1328_);
                        crate::leanh::lean_ctor_set(v___x_1495_, 0, v___x_1543_);
                        v___x_1545_ = v___x_1495_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_1558_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1543_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1328_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1329_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_r_1485_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_r_1331_);
                        v___x_1545_ = v_reuseFailAlloc_1558_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1509_ = lean_nat_add(v___x_1479_, v_size_1481_);
                crate::leanh::lean_dec(v_size_1481_);
                v___x_1510_ = lean_nat_add(v___x_1509_, v_size_1480_);
                crate::leanh::lean_dec(v___x_1509_);
                v___x_1522_ = lean_nat_add(v___x_1479_, v_size_1497_);
                if crate::leanh::lean_obj_tag(v_l_1501_) == 0 {
                    v_size_1532_ = crate::leanh::lean_ctor_get(v_l_1501_, 0);
                    crate::leanh::lean_inc(v_size_1532_);
                    v___y_1524_ = v_size_1532_;
                    state = 29;
                    continue;
                } else {
                    v___x_1533_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1524_ = v___x_1533_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_1515_ = lean_nat_add(v___y_1513_, v___y_1514_);
                crate::leanh::lean_dec(v___y_1514_);
                crate::leanh::lean_dec(v___y_1513_);
                if v_isShared_1508_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1507_, 4, v_r_1331_);
                    crate::leanh::lean_ctor_set(v___x_1507_, 3, v_r_1502_);
                    crate::leanh::lean_ctor_set(v___x_1507_, 2, v_v_1329_);
                    crate::leanh::lean_ctor_set(v___x_1507_, 1, v_k_1328_);
                    crate::leanh::lean_ctor_set(v___x_1507_, 0, v___x_1515_);
                    v___x_1517_ = v___x_1507_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1521_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_k_1328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_v_1329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_r_1502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 4, v_r_1331_);
                    v___x_1517_ = v_reuseFailAlloc_1521_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1496_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1495_, 4, v___x_1517_);
                    crate::leanh::lean_ctor_set(v___x_1495_, 3, v___y_1512_);
                    crate::leanh::lean_ctor_set(v___x_1495_, 2, v_v_1500_);
                    crate::leanh::lean_ctor_set(v___x_1495_, 1, v_k_1499_);
                    crate::leanh::lean_ctor_set(v___x_1495_, 0, v___x_1510_);
                    v___x_1519_ = v___x_1495_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1520_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1510_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_k_1499_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_v_1500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1520_, 3, v___y_1512_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1520_, 4, v___x_1517_);
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
                crate::leanh::lean_dec(v___y_1524_);
                crate::leanh::lean_dec(v___x_1522_);
                if v_isShared_1334_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1333_, 4, v_l_1501_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 3, v_l_1484_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 2, v_v_1483_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 1, v_k_1482_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1525_);
                    v___x_1527_ = v___x_1333_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1531_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1525_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_k_1482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_v_1483_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_l_1484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_l_1501_);
                    v___x_1527_ = v_reuseFailAlloc_1531_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1528_ = lean_nat_add(v___x_1479_, v_size_1480_);
                if crate::leanh::lean_obj_tag(v_r_1502_) == 0 {
                    v_size_1529_ = crate::leanh::lean_ctor_get(v_r_1502_, 0);
                    crate::leanh::lean_inc(v_size_1529_);
                    v___y_1512_ = v___x_1527_;
                    v___y_1513_ = v___x_1528_;
                    v___y_1514_ = v_size_1529_;
                    state = 26;
                    continue;
                } else {
                    v___x_1530_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1512_ = v___x_1527_;
                    v___y_1513_ = v___x_1528_;
                    v___y_1514_ = v___x_1530_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_1552_ = (!crate::leanh::lean_is_exclusive(v_r_1331_)) as u8;
                if v_isSharedCheck_1552_ == 0 {
                    v_unused_1553_ = crate::leanh::lean_ctor_get(v_r_1331_, 4);
                    crate::leanh::lean_dec(v_unused_1553_);
                    v_unused_1554_ = crate::leanh::lean_ctor_get(v_r_1331_, 3);
                    crate::leanh::lean_dec(v_unused_1554_);
                    v_unused_1555_ = crate::leanh::lean_ctor_get(v_r_1331_, 2);
                    crate::leanh::lean_dec(v_unused_1555_);
                    v_unused_1556_ = crate::leanh::lean_ctor_get(v_r_1331_, 1);
                    crate::leanh::lean_dec(v_unused_1556_);
                    v_unused_1557_ = crate::leanh::lean_ctor_get(v_r_1331_, 0);
                    crate::leanh::lean_dec(v_unused_1557_);
                    v___x_1547_ = v_r_1331_;
                    v_isShared_1548_ = v_isSharedCheck_1552_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_1331_);
                    v___x_1547_ = crate::leanh::lean_box(0);
                    v_isShared_1548_ = v_isSharedCheck_1552_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1548_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1547_, 4, v___x_1545_);
                    crate::leanh::lean_ctor_set(v___x_1547_, 3, v_l_1484_);
                    crate::leanh::lean_ctor_set(v___x_1547_, 2, v_v_1483_);
                    crate::leanh::lean_ctor_set(v___x_1547_, 1, v_k_1482_);
                    crate::leanh::lean_ctor_set(v___x_1547_, 0, v___x_1541_);
                    v___x_1550_ = v___x_1547_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1551_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_k_1482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1551_, 2, v_v_1483_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1551_, 3, v_l_1484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1551_, 4, v___x_1545_);
                    v___x_1550_ = v_reuseFailAlloc_1551_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1550_;
            }
            34 => {
                v___x_1572_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_1566_);
                if v_isShared_1571_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1570_, 3, v_r_1566_);
                    crate::leanh::lean_ctor_set(v___x_1570_, 2, v_v_1329_);
                    crate::leanh::lean_ctor_set(v___x_1570_, 1, v_k_1328_);
                    crate::leanh::lean_ctor_set(v___x_1570_, 0, v___x_1479_);
                    v___x_1574_ = v___x_1570_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1578_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_k_1328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_v_1329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 3, v_r_1566_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 4, v_r_1566_);
                    v___x_1574_ = v_reuseFailAlloc_1578_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_1334_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1333_, 4, v___x_1574_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 3, v_l_1565_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 2, v_v_1568_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 1, v_k_1567_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1572_);
                    v___x_1576_ = v___x_1333_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1577_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1572_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_k_1567_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_v_1568_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 3, v_l_1565_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 4, v___x_1574_);
                    v___x_1576_ = v_reuseFailAlloc_1577_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_1576_;
            }
            37 => {
                v_k_1588_ = crate::leanh::lean_ctor_get(v_r_1582_, 1);
                v_v_1589_ = crate::leanh::lean_ctor_get(v_r_1582_, 2);
                v_isSharedCheck_1603_ = (!crate::leanh::lean_is_exclusive(v_r_1582_)) as u8;
                if v_isSharedCheck_1603_ == 0 {
                    v_unused_1604_ = crate::leanh::lean_ctor_get(v_r_1582_, 4);
                    crate::leanh::lean_dec(v_unused_1604_);
                    v_unused_1605_ = crate::leanh::lean_ctor_get(v_r_1582_, 3);
                    crate::leanh::lean_dec(v_unused_1605_);
                    v_unused_1606_ = crate::leanh::lean_ctor_get(v_r_1582_, 0);
                    crate::leanh::lean_dec(v_unused_1606_);
                    v___x_1591_ = v_r_1582_;
                    v_isShared_1592_ = v_isSharedCheck_1603_;
                    state = 38;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1589_);
                    crate::leanh::lean_inc(v_k_1588_);
                    crate::leanh::lean_dec(v_r_1582_);
                    v___x_1591_ = crate::leanh::lean_box(0);
                    v_isShared_1592_ = v_isSharedCheck_1603_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_1593_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_1592_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1591_, 4, v_l_1565_);
                    crate::leanh::lean_ctor_set(v___x_1591_, 3, v_l_1565_);
                    crate::leanh::lean_ctor_set(v___x_1591_, 2, v_v_1584_);
                    crate::leanh::lean_ctor_set(v___x_1591_, 1, v_k_1583_);
                    crate::leanh::lean_ctor_set(v___x_1591_, 0, v___x_1479_);
                    v___x_1595_ = v___x_1591_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_k_1583_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_v_1584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 3, v_l_1565_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 4, v_l_1565_);
                    v___x_1595_ = v_reuseFailAlloc_1602_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_1587_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1586_, 4, v_l_1565_);
                    crate::leanh::lean_ctor_set(v___x_1586_, 2, v_v_1329_);
                    crate::leanh::lean_ctor_set(v___x_1586_, 1, v_k_1328_);
                    crate::leanh::lean_ctor_set(v___x_1586_, 0, v___x_1479_);
                    v___x_1597_ = v___x_1586_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1601_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_k_1328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_v_1329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_l_1565_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_l_1565_);
                    v___x_1597_ = v_reuseFailAlloc_1601_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1334_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1333_, 4, v___x_1597_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 3, v___x_1595_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 2, v_v_1589_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 1, v_k_1588_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1593_);
                    v___x_1599_ = v___x_1333_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1600_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1593_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_k_1588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_v_1589_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 3, v___x_1595_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 4, v___x_1597_);
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
    mut v_k_1619_: *mut crate::leanh::LeanObject,
    mut v_v_1620_: *mut crate::leanh::LeanObject,
    mut v_t_1621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_boxed_1622_: u64 = 0;
    let mut v_res_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_1622_ = crate::leanh::lean_unbox_uint64(v_k_1619_);
    crate::leanh::lean_dec_ref(v_k_1619_);
    v_res_1623_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(
            v_k_boxed_1622_,
            v_v_1620_,
            v_t_1621_,
        );
    return v_res_1623_;
}
pub unsafe fn l_Std_CancellationContext_new() -> *mut crate::leanh::LeanObject {
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: u64 = 0;
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: u64 = 0;
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_Std_CancellationToken_new();
    v___x_1628_ = crate::leanh::lean_box(1);
    v___x_1629_ = 0u64;
    v___x_1630_ = l_Std_CancellationContext_new___closed__0;
    crate::leanh::lean_inc_ref(v___x_1627_);
    v___x_1631_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1631_, 0, v___x_1627_);
    crate::leanh::lean_ctor_set(v___x_1631_, 1, v___x_1630_);
    v___x_1632_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(
            v___x_1629_,
            v___x_1631_,
            v___x_1628_,
        );
    v___x_1633_ = 1u64;
    v___x_1634_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_1634_, 0, v___x_1632_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_1634_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1633_,
    );
    v___x_1635_ = l_Std_Mutex_new___redArg(v___x_1634_);
    v___x_1636_ = crate::leanh::lean_alloc_ctor(0, 2, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_1636_, 0, v___x_1635_);
    crate::leanh::lean_ctor_set(v___x_1636_, 1, v___x_1627_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_1636_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v___x_1629_,
    );
    return v___x_1636_;
}
pub unsafe fn l_Std_CancellationContext_new___boxed(
    mut v_a_1637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1638_ = l_Std_CancellationContext_new();
    return v_res_1638_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0(
    mut v_00_u03b2_1639_: *mut crate::leanh::LeanObject,
    mut v_k_1640_: u64,
    mut v_v_1641_: *mut crate::leanh::LeanObject,
    mut v_t_1642_: *mut crate::leanh::LeanObject,
    mut v_hl_1643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1644_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(
            v_k_1640_, v_v_1641_, v_t_1642_,
        );
    return v___x_1644_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___boxed(
    mut v_00_u03b2_1645_: *mut crate::leanh::LeanObject,
    mut v_k_1646_: *mut crate::leanh::LeanObject,
    mut v_v_1647_: *mut crate::leanh::LeanObject,
    mut v_t_1648_: *mut crate::leanh::LeanObject,
    mut v_hl_1649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_boxed_1650_: u64 = 0;
    let mut v_res_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_1650_ = crate::leanh::lean_unbox_uint64(v_k_1646_);
    crate::leanh::lean_dec_ref(v_k_1646_);
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
    mut v_mutex_1652_: *mut crate::leanh::LeanObject,
    mut v_k_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1655_ = crate::leanh::lean_ctor_get(v_mutex_1652_, 0);
    crate::leanh::lean_inc(v_ref_1655_);
    v_mutex_1656_ = crate::leanh::lean_ctor_get(v_mutex_1652_, 1);
    crate::leanh::lean_inc(v_mutex_1656_);
    crate::leanh::lean_dec_ref(v_mutex_1652_);
    v___x_1657_ = lean_io_basemutex_lock(v_mutex_1656_);
    v___x_1658_ = crate::leanh::lean_apply_2(v_k_1653_, v_ref_1655_, crate::leanh::lean_box(0));
    v___x_1659_ = lean_io_basemutex_unlock(v_mutex_1656_);
    crate::leanh::lean_dec(v_mutex_1656_);
    return v___x_1658_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg___boxed(
    mut v_mutex_1660_: *mut crate::leanh::LeanObject,
    mut v_k_1661_: *mut crate::leanh::LeanObject,
    mut v___y_1662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1663_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(
        v_mutex_1660_,
        v_k_1661_,
    );
    return v_res_1663_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(
    mut v_00_u03b1_1664_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1665_: *mut crate::leanh::LeanObject,
    mut v_mutex_1666_: *mut crate::leanh::LeanObject,
    mut v_k_1667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1669_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(
        v_mutex_1666_,
        v_k_1667_,
    );
    return v___x_1669_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___boxed(
    mut v_00_u03b1_1670_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1671_: *mut crate::leanh::LeanObject,
    mut v_mutex_1672_: *mut crate::leanh::LeanObject,
    mut v_k_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1675_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1(
        v_00_u03b1_1670_,
        v_00_u03b2_1671_,
        v_mutex_1672_,
        v_k_1673_,
    );
    return v_res_1675_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(
    mut v_x_1676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_x_1676_);
    return v_x_1676_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0___boxed(
    mut v_x_1677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1678_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__0(v_x_1677_);
    crate::leanh::lean_dec_ref(v_x_1677_);
    return v_res_1678_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(
    mut v___x_1679_: u64,
    mut v_x_1680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1681_ = crate::leanh::lean_box_uint64(v___x_1679_);
    v___x_1682_ = lean_array_push(v_x_1680_, v___x_1681_);
    return v___x_1682_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed(
    mut v___x_1683_: *mut crate::leanh::LeanObject,
    mut v_x_1684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1350__boxed_1685_: u64 = 0;
    let mut v_res_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1350__boxed_1685_ = crate::leanh::lean_unbox_uint64(v___x_1683_);
    crate::leanh::lean_dec_ref(v___x_1683_);
    v_res_1686_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1(v___x_1350__boxed_1685_, v_x_1684_);
    return v_res_1686_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(
    mut v___x_1688_: u64,
    mut v_k_1689_: u64,
    mut v_t_1690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1698_: u8 = 0;
    let mut v___x_1699_: u64 = 0;
    let mut v___x_1700_: u8 = 0;
    let mut v___x_1701_: u64 = 0;
    let mut v___x_1702_: u8 = 0;
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1690_) == 0 {
                    v_size_1691_ = crate::leanh::lean_ctor_get(v_t_1690_, 0);
                    v_k_1692_ = crate::leanh::lean_ctor_get(v_t_1690_, 1);
                    v_v_1693_ = crate::leanh::lean_ctor_get(v_t_1690_, 2);
                    v_l_1694_ = crate::leanh::lean_ctor_get(v_t_1690_, 3);
                    v_r_1695_ = crate::leanh::lean_ctor_get(v_t_1690_, 4);
                    v_isSharedCheck_1719_ = (!crate::leanh::lean_is_exclusive(v_t_1690_)) as u8;
                    if v_isSharedCheck_1719_ == 0 {
                        v___x_1697_ = v_t_1690_;
                        v_isShared_1698_ = v_isSharedCheck_1719_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1695_);
                        crate::leanh::lean_inc(v_l_1694_);
                        crate::leanh::lean_inc(v_v_1693_);
                        crate::leanh::lean_inc(v_k_1692_);
                        crate::leanh::lean_inc(v_size_1691_);
                        crate::leanh::lean_dec(v_t_1690_);
                        v___x_1697_ = crate::leanh::lean_box(0);
                        v_isShared_1698_ = v_isSharedCheck_1719_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_t_1690_;
                }
            }
            1 => {
                v___x_1699_ = crate::leanh::lean_unbox_uint64(v_k_1692_);
                v___x_1700_ = lean_uint64_dec_lt(v_k_1689_, v___x_1699_);
                if v___x_1700_ == 0 {
                    v___x_1701_ = crate::leanh::lean_unbox_uint64(v_k_1692_);
                    v___x_1702_ = lean_uint64_dec_eq(v_k_1689_, v___x_1701_);
                    if v___x_1702_ == 0 {
                        v___x_1703_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v___x_1688_, v_k_1689_, v_r_1695_);
                        if v_isShared_1698_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1697_, 4, v___x_1703_);
                            v___x_1705_ = v___x_1697_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1706_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_size_1691_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_k_1692_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_v_1693_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 3, v_l_1694_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 4, v___x_1703_);
                            v___x_1705_ = v_reuseFailAlloc_1706_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_k_1692_);
                        v___f_1707_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___closed__0;
                        v___x_1708_ = crate::leanh::lean_box_uint64(v___x_1688_);
                        v___f_1709_ = crate::leanh::lean_alloc_closure(l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                        crate::leanh::lean_closure_set(v___f_1709_, 0, v___x_1708_);
                        v___x_1710_ = l_Prod_map___redArg(v___f_1707_, v___f_1709_, v_v_1693_);
                        v___x_1711_ = crate::leanh::lean_box_uint64(v_k_1689_);
                        if v_isShared_1698_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1697_, 2, v___x_1710_);
                            crate::leanh::lean_ctor_set(v___x_1697_, 1, v___x_1711_);
                            v___x_1713_ = v___x_1697_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1714_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_size_1691_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 1, v___x_1711_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 2, v___x_1710_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 3, v_l_1694_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 4, v_r_1695_);
                            v___x_1713_ = v_reuseFailAlloc_1714_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_1715_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v___x_1688_, v_k_1689_, v_l_1694_);
                    if v_isShared_1698_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1697_, 3, v___x_1715_);
                        v___x_1717_ = v___x_1697_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1718_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_size_1691_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_k_1692_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 2, v_v_1693_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 3, v___x_1715_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 4, v_r_1695_);
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
    mut v___x_1720_: *mut crate::leanh::LeanObject,
    mut v_k_1721_: *mut crate::leanh::LeanObject,
    mut v_t_1722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1362__boxed_1723_: u64 = 0;
    let mut v_k_boxed_1724_: u64 = 0;
    let mut v_res_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1362__boxed_1723_ = crate::leanh::lean_unbox_uint64(v___x_1720_);
    crate::leanh::lean_dec_ref(v___x_1720_);
    v_k_boxed_1724_ = crate::leanh::lean_unbox_uint64(v_k_1721_);
    crate::leanh::lean_dec_ref(v_k_1721_);
    v_res_1725_ =
        l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(
            v___x_1362__boxed_1723_,
            v_k_boxed_1724_,
            v_t_1722_,
        );
    return v_res_1725_;
}
pub unsafe fn l_Std_CancellationContext_fork___lam__0(
    mut v_token_1726_: *mut crate::leanh::LeanObject,
    mut v_id_1727_: u64,
    mut v_state_1728_: *mut crate::leanh::LeanObject,
    mut v_root_1729_: *mut crate::leanh::LeanObject,
    mut v___y_1730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1732_: u8 = 0;
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tokens_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1736_: u64 = 0;
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: u64 = 0;
    let mut v___x_1745_: u64 = 0;
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1732_ = l_Std_CancellationToken_isCancelled(v_token_1726_);
                if v___x_1732_ == 0 {
                    v___x_1733_ = l_Std_CancellationToken_new();
                    v___x_1734_ = lean_st_ref_get(v___y_1730_);
                    v_tokens_1735_ = crate::leanh::lean_ctor_get(v___x_1734_, 0);
                    v_id_1736_ = crate::leanh::lean_ctor_get_uint64(
                        v___x_1734_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_isSharedCheck_1751_ = (!crate::leanh::lean_is_exclusive(v___x_1734_)) as u8;
                    if v_isSharedCheck_1751_ == 0 {
                        v___x_1738_ = v___x_1734_;
                        v_isShared_1739_ = v_isSharedCheck_1751_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tokens_1735_);
                        crate::leanh::lean_dec(v___x_1734_);
                        v___x_1738_ = crate::leanh::lean_box(0);
                        v_isShared_1739_ = v_isSharedCheck_1751_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_state_1728_);
                    crate::leanh::lean_inc_ref(v_root_1729_);
                    return v_root_1729_;
                }
            }
            1 => {
                v___x_1740_ = l_Std_CancellationContext_new___closed__0;
                crate::leanh::lean_inc_ref(v___x_1733_);
                v___x_1741_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1741_, 0, v___x_1733_);
                crate::leanh::lean_ctor_set(v___x_1741_, 1, v___x_1740_);
                v___x_1742_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_CancellationContext_new_spec__0___redArg(v_id_1736_, v___x_1741_, v_tokens_1735_);
                v___x_1743_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Std_CancellationContext_fork_spec__0(v_id_1736_, v_id_1727_, v___x_1742_);
                v___x_1744_ = 1u64;
                v___x_1745_ = lean_uint64_add(v_id_1736_, v___x_1744_);
                if v_isShared_1739_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1738_, 0, v___x_1743_);
                    v___x_1747_ = v___x_1738_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1750_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1743_);
                    v___x_1747_ = v_reuseFailAlloc_1750_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint64(
                    v___x_1747_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1745_,
                );
                v___x_1748_ = lean_st_ref_set(v___y_1730_, v___x_1747_);
                v___x_1749_ = crate::leanh::lean_alloc_ctor(0, 2, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_1749_, 0, v_state_1728_);
                crate::leanh::lean_ctor_set(v___x_1749_, 1, v___x_1733_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_1749_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_id_1736_,
                );
                return v___x_1749_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CancellationContext_fork___lam__0___boxed(
    mut v_token_1752_: *mut crate::leanh::LeanObject,
    mut v_id_1753_: *mut crate::leanh::LeanObject,
    mut v_state_1754_: *mut crate::leanh::LeanObject,
    mut v_root_1755_: *mut crate::leanh::LeanObject,
    mut v___y_1756_: *mut crate::leanh::LeanObject,
    mut v___y_1757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_boxed_1758_: u64 = 0;
    let mut v_res_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_id_boxed_1758_ = crate::leanh::lean_unbox_uint64(v_id_1753_);
    crate::leanh::lean_dec_ref(v_id_1753_);
    v_res_1759_ = l_Std_CancellationContext_fork___lam__0(
        v_token_1752_,
        v_id_boxed_1758_,
        v_state_1754_,
        v_root_1755_,
        v___y_1756_,
    );
    crate::leanh::lean_dec(v___y_1756_);
    crate::leanh::lean_dec_ref(v_root_1755_);
    return v_res_1759_;
}
pub unsafe fn l_Std_CancellationContext_fork(
    mut v_root_1760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_state_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_token_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1764_: u64 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_state_1762_ = crate::leanh::lean_ctor_get(v_root_1760_, 0);
    crate::leanh::lean_inc_ref_n(v_state_1762_, 2);
    v_token_1763_ = crate::leanh::lean_ctor_get(v_root_1760_, 1);
    crate::leanh::lean_inc_ref(v_token_1763_);
    v_id_1764_ = crate::leanh::lean_ctor_get_uint64(
        v_root_1760_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    v___x_1765_ = crate::leanh::lean_box_uint64(v_id_1764_);
    v___f_1766_ = crate::leanh::lean_alloc_closure(
        l_Std_CancellationContext_fork___lam__0___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1766_, 0, v_token_1763_);
    crate::leanh::lean_closure_set(v___f_1766_, 1, v___x_1765_);
    crate::leanh::lean_closure_set(v___f_1766_, 2, v_state_1762_);
    crate::leanh::lean_closure_set(v___f_1766_, 3, v_root_1760_);
    v___x_1767_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(
        v_state_1762_,
        v___f_1766_,
    );
    return v___x_1767_;
}
pub unsafe fn l_Std_CancellationContext_fork___boxed(
    mut v_root_1768_: *mut crate::leanh::LeanObject,
    mut v_a_1769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1770_ = l_Std_CancellationContext_fork(v_root_1768_);
    return v_res_1770_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(
    mut v_k_1771_: u64,
    mut v_t_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1779_: u8 = 0;
    let mut v___x_1780_: u64 = 0;
    let mut v___x_1781_: u8 = 0;
    let mut v___x_1782_: u64 = 0;
    let mut v___x_1783_: u8 = 0;
    let mut v_impl_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: u8 = 0;
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1802_: u8 = 0;
    let mut v_size_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1814_: u8 = 0;
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1840_: u8 = 0;
    let mut v_unused_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1854_: u8 = 0;
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut v_unused_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1865_: u8 = 0;
    let mut v_unused_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1883_: u8 = 0;
    let mut v_size_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1893_: u8 = 0;
    let mut v_unused_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1900_: u8 = 0;
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1908_: u8 = 0;
    let mut v_unused_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v_k_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1933_: u8 = 0;
    let mut v_unused_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1937_: u8 = 0;
    let mut v_unused_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1962_: u8 = 0;
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: u8 = 0;
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v_size_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: u8 = 0;
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1990_: u8 = 0;
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2015_: u8 = 0;
    let mut v_unused_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2030_: u8 = 0;
    let mut v_unused_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v_k_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2056_: u8 = 0;
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2067_: u8 = 0;
    let mut v_unused_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2089_: u8 = 0;
    let mut v_unused_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2095_: u8 = 0;
    let mut v_unused_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2103_: u8 = 0;
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: u8 = 0;
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2119_: u8 = 0;
    let mut v_size_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: u8 = 0;
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2131_: u8 = 0;
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2143_: u8 = 0;
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2147_: u8 = 0;
    let mut v_unused_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2166_: u8 = 0;
    let mut v_unused_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2182_: u8 = 0;
    let mut v_unused_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2190_: u8 = 0;
    let mut v_k_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2211_: u8 = 0;
    let mut v_unused_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2219_: u8 = 0;
    let mut v_k_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2226_: u8 = 0;
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut v_unused_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut v_unused_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2253_: u8 = 0;
    let mut v_unused_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: u8 = 0;
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2277_: u8 = 0;
    let mut v_size_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: u8 = 0;
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2289_: u8 = 0;
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2314_: u8 = 0;
    let mut v_unused_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2327_: u8 = 0;
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2331_: u8 = 0;
    let mut v_unused_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2338_: u8 = 0;
    let mut v_unused_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v_size_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2366_: u8 = 0;
    let mut v_unused_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2373_: u8 = 0;
    let mut v_k_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2378_: u8 = 0;
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2389_: u8 = 0;
    let mut v_unused_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2393_: u8 = 0;
    let mut v_unused_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2402_: u8 = 0;
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2410_: u8 = 0;
    let mut v_unused_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2419_: u8 = 0;
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut v_unused_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2433_: u8 = 0;
    let mut v_unused_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1772_) == 0 {
                    v_k_1773_ = crate::leanh::lean_ctor_get(v_t_1772_, 1);
                    v_v_1774_ = crate::leanh::lean_ctor_get(v_t_1772_, 2);
                    v_l_1775_ = crate::leanh::lean_ctor_get(v_t_1772_, 3);
                    v_r_1776_ = crate::leanh::lean_ctor_get(v_t_1772_, 4);
                    v_isSharedCheck_2433_ = (!crate::leanh::lean_is_exclusive(v_t_1772_)) as u8;
                    if v_isSharedCheck_2433_ == 0 {
                        v_unused_2434_ = crate::leanh::lean_ctor_get(v_t_1772_, 0);
                        crate::leanh::lean_dec(v_unused_2434_);
                        v___x_1778_ = v_t_1772_;
                        v_isShared_1779_ = v_isSharedCheck_2433_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1776_);
                        crate::leanh::lean_inc(v_l_1775_);
                        crate::leanh::lean_inc(v_v_1774_);
                        crate::leanh::lean_inc(v_k_1773_);
                        crate::leanh::lean_dec(v_t_1772_);
                        v___x_1778_ = crate::leanh::lean_box(0);
                        v_isShared_1779_ = v_isSharedCheck_2433_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_t_1772_;
                }
            }
            1 => {
                v___x_1780_ = crate::leanh::lean_unbox_uint64(v_k_1773_);
                v___x_1781_ = lean_uint64_dec_lt(v_k_1771_, v___x_1780_);
                if v___x_1781_ == 0 {
                    v___x_1782_ = crate::leanh::lean_unbox_uint64(v_k_1773_);
                    v___x_1783_ = lean_uint64_dec_eq(v_k_1771_, v___x_1782_);
                    if v___x_1783_ == 0 {
                        v_impl_1784_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_1771_, v_r_1776_);
                        v___x_1785_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_impl_1784_) == 0 {
                            if crate::leanh::lean_obj_tag(v_l_1775_) == 0 {
                                v_size_1786_ = crate::leanh::lean_ctor_get(v_impl_1784_, 0);
                                crate::leanh::lean_inc(v_size_1786_);
                                v_size_1787_ = crate::leanh::lean_ctor_get(v_l_1775_, 0);
                                v_k_1788_ = crate::leanh::lean_ctor_get(v_l_1775_, 1);
                                v_v_1789_ = crate::leanh::lean_ctor_get(v_l_1775_, 2);
                                v_l_1790_ = crate::leanh::lean_ctor_get(v_l_1775_, 3);
                                v_r_1791_ = crate::leanh::lean_ctor_get(v_l_1775_, 4);
                                crate::leanh::lean_inc(v_r_1791_);
                                v___x_1792_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_1793_ = lean_nat_mul(v___x_1792_, v_size_1786_);
                                v___x_1794_ = lean_nat_dec_lt(v___x_1793_, v_size_1787_);
                                crate::leanh::lean_dec(v___x_1793_);
                                if v___x_1794_ == 0 {
                                    crate::leanh::lean_dec(v_r_1791_);
                                    v___x_1795_ = lean_nat_add(v___x_1785_, v_size_1787_);
                                    v___x_1796_ = lean_nat_add(v___x_1795_, v_size_1786_);
                                    crate::leanh::lean_dec(v_size_1786_);
                                    crate::leanh::lean_dec(v___x_1795_);
                                    if v_isShared_1779_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1778_, 4, v_impl_1784_);
                                        crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_1796_);
                                        v___x_1798_ = v___x_1778_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1799_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1799_,
                                            0,
                                            v___x_1796_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1799_,
                                            1,
                                            v_k_1773_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1799_,
                                            2,
                                            v_v_1774_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1799_,
                                            3,
                                            v_l_1775_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1799_,
                                            4,
                                            v_impl_1784_,
                                        );
                                        v___x_1798_ = v_reuseFailAlloc_1799_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_l_1790_);
                                    crate::leanh::lean_inc(v_v_1789_);
                                    crate::leanh::lean_inc(v_k_1788_);
                                    crate::leanh::lean_inc(v_size_1787_);
                                    v_isSharedCheck_1865_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_1775_)) as u8;
                                    if v_isSharedCheck_1865_ == 0 {
                                        v_unused_1866_ = crate::leanh::lean_ctor_get(v_l_1775_, 4);
                                        crate::leanh::lean_dec(v_unused_1866_);
                                        v_unused_1867_ = crate::leanh::lean_ctor_get(v_l_1775_, 3);
                                        crate::leanh::lean_dec(v_unused_1867_);
                                        v_unused_1868_ = crate::leanh::lean_ctor_get(v_l_1775_, 2);
                                        crate::leanh::lean_dec(v_unused_1868_);
                                        v_unused_1869_ = crate::leanh::lean_ctor_get(v_l_1775_, 1);
                                        crate::leanh::lean_dec(v_unused_1869_);
                                        v_unused_1870_ = crate::leanh::lean_ctor_get(v_l_1775_, 0);
                                        crate::leanh::lean_dec(v_unused_1870_);
                                        v___x_1801_ = v_l_1775_;
                                        v_isShared_1802_ = v_isSharedCheck_1865_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_1775_);
                                        v___x_1801_ = crate::leanh::lean_box(0);
                                        v_isShared_1802_ = v_isSharedCheck_1865_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_1871_ = crate::leanh::lean_ctor_get(v_impl_1784_, 0);
                                crate::leanh::lean_inc(v_size_1871_);
                                v___x_1872_ = lean_nat_add(v___x_1785_, v_size_1871_);
                                crate::leanh::lean_dec(v_size_1871_);
                                if v_isShared_1779_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1778_, 4, v_impl_1784_);
                                    crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_1872_);
                                    v___x_1874_ = v___x_1778_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1875_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1875_,
                                        0,
                                        v___x_1872_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1875_,
                                        1,
                                        v_k_1773_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1875_,
                                        2,
                                        v_v_1774_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1875_,
                                        3,
                                        v_l_1775_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                            if crate::leanh::lean_obj_tag(v_l_1775_) == 0 {
                                v_l_1876_ = crate::leanh::lean_ctor_get(v_l_1775_, 3);
                                if crate::leanh::lean_obj_tag(v_l_1876_) == 0 {
                                    crate::leanh::lean_inc_ref(v_l_1876_);
                                    v_r_1877_ = crate::leanh::lean_ctor_get(v_l_1775_, 4);
                                    crate::leanh::lean_inc(v_r_1877_);
                                    if crate::leanh::lean_obj_tag(v_r_1877_) == 0 {
                                        v_size_1878_ = crate::leanh::lean_ctor_get(v_l_1775_, 0);
                                        v_k_1879_ = crate::leanh::lean_ctor_get(v_l_1775_, 1);
                                        v_v_1880_ = crate::leanh::lean_ctor_get(v_l_1775_, 2);
                                        v_isSharedCheck_1893_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_1775_)) as u8;
                                        if v_isSharedCheck_1893_ == 0 {
                                            v_unused_1894_ =
                                                crate::leanh::lean_ctor_get(v_l_1775_, 4);
                                            crate::leanh::lean_dec(v_unused_1894_);
                                            v_unused_1895_ =
                                                crate::leanh::lean_ctor_get(v_l_1775_, 3);
                                            crate::leanh::lean_dec(v_unused_1895_);
                                            v___x_1882_ = v_l_1775_;
                                            v_isShared_1883_ = v_isSharedCheck_1893_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1880_);
                                            crate::leanh::lean_inc(v_k_1879_);
                                            crate::leanh::lean_inc(v_size_1878_);
                                            crate::leanh::lean_dec(v_l_1775_);
                                            v___x_1882_ = crate::leanh::lean_box(0);
                                            v_isShared_1883_ = v_isSharedCheck_1893_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_1896_ = crate::leanh::lean_ctor_get(v_l_1775_, 1);
                                        v_v_1897_ = crate::leanh::lean_ctor_get(v_l_1775_, 2);
                                        v_isSharedCheck_1908_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_1775_)) as u8;
                                        if v_isSharedCheck_1908_ == 0 {
                                            v_unused_1909_ =
                                                crate::leanh::lean_ctor_get(v_l_1775_, 4);
                                            crate::leanh::lean_dec(v_unused_1909_);
                                            v_unused_1910_ =
                                                crate::leanh::lean_ctor_get(v_l_1775_, 3);
                                            crate::leanh::lean_dec(v_unused_1910_);
                                            v_unused_1911_ =
                                                crate::leanh::lean_ctor_get(v_l_1775_, 0);
                                            crate::leanh::lean_dec(v_unused_1911_);
                                            v___x_1899_ = v_l_1775_;
                                            v_isShared_1900_ = v_isSharedCheck_1908_;
                                            state = 17;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1897_);
                                            crate::leanh::lean_inc(v_k_1896_);
                                            crate::leanh::lean_dec(v_l_1775_);
                                            v___x_1899_ = crate::leanh::lean_box(0);
                                            v_isShared_1900_ = v_isSharedCheck_1908_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_1912_ = crate::leanh::lean_ctor_get(v_l_1775_, 4);
                                    crate::leanh::lean_inc(v_r_1912_);
                                    if crate::leanh::lean_obj_tag(v_r_1912_) == 0 {
                                        crate::leanh::lean_inc(v_l_1876_);
                                        v_k_1913_ = crate::leanh::lean_ctor_get(v_l_1775_, 1);
                                        v_v_1914_ = crate::leanh::lean_ctor_get(v_l_1775_, 2);
                                        v_isSharedCheck_1937_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_1775_)) as u8;
                                        if v_isSharedCheck_1937_ == 0 {
                                            v_unused_1938_ =
                                                crate::leanh::lean_ctor_get(v_l_1775_, 4);
                                            crate::leanh::lean_dec(v_unused_1938_);
                                            v_unused_1939_ =
                                                crate::leanh::lean_ctor_get(v_l_1775_, 3);
                                            crate::leanh::lean_dec(v_unused_1939_);
                                            v_unused_1940_ =
                                                crate::leanh::lean_ctor_get(v_l_1775_, 0);
                                            crate::leanh::lean_dec(v_unused_1940_);
                                            v___x_1916_ = v_l_1775_;
                                            v_isShared_1917_ = v_isSharedCheck_1937_;
                                            state = 20;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1914_);
                                            crate::leanh::lean_inc(v_k_1913_);
                                            crate::leanh::lean_dec(v_l_1775_);
                                            v___x_1916_ = crate::leanh::lean_box(0);
                                            v_isShared_1917_ = v_isSharedCheck_1937_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_1941_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_1779_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_1778_, 4, v_r_1912_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1778_,
                                                0,
                                                v___x_1941_,
                                            );
                                            v___x_1943_ = v___x_1778_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_1944_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1944_,
                                                0,
                                                v___x_1941_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1944_,
                                                1,
                                                v_k_1773_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1944_,
                                                2,
                                                v_v_1774_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1944_,
                                                3,
                                                v_l_1775_,
                                            );
                                            crate::leanh::lean_ctor_set(
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
                                    crate::leanh::lean_ctor_set(v___x_1778_, 4, v_l_1775_);
                                    crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_1785_);
                                    v___x_1946_ = v___x_1778_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1947_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1947_,
                                        0,
                                        v___x_1785_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1947_,
                                        1,
                                        v_k_1773_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1947_,
                                        2,
                                        v_v_1774_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1947_,
                                        3,
                                        v_l_1775_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                        crate::leanh::lean_del_object(v___x_1778_);
                        crate::leanh::lean_dec(v_v_1774_);
                        crate::leanh::lean_dec(v_k_1773_);
                        if crate::leanh::lean_obj_tag(v_l_1775_) == 0 {
                            if crate::leanh::lean_obj_tag(v_r_1776_) == 0 {
                                v_size_1948_ = crate::leanh::lean_ctor_get(v_l_1775_, 0);
                                v_k_1949_ = crate::leanh::lean_ctor_get(v_l_1775_, 1);
                                v_v_1950_ = crate::leanh::lean_ctor_get(v_l_1775_, 2);
                                v_l_1951_ = crate::leanh::lean_ctor_get(v_l_1775_, 3);
                                v_r_1952_ = crate::leanh::lean_ctor_get(v_l_1775_, 4);
                                crate::leanh::lean_inc(v_r_1952_);
                                v_size_1953_ = crate::leanh::lean_ctor_get(v_r_1776_, 0);
                                v_k_1954_ = crate::leanh::lean_ctor_get(v_r_1776_, 1);
                                v_v_1955_ = crate::leanh::lean_ctor_get(v_r_1776_, 2);
                                v_l_1956_ = crate::leanh::lean_ctor_get(v_r_1776_, 3);
                                crate::leanh::lean_inc(v_l_1956_);
                                v_r_1957_ = crate::leanh::lean_ctor_get(v_r_1776_, 4);
                                v___x_1958_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_1959_ = lean_nat_dec_lt(v_size_1948_, v_size_1953_);
                                if v___x_1959_ == 0 {
                                    crate::leanh::lean_inc(v_l_1951_);
                                    crate::leanh::lean_inc(v_v_1950_);
                                    crate::leanh::lean_inc(v_k_1949_);
                                    v_isSharedCheck_2095_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_1775_)) as u8;
                                    if v_isSharedCheck_2095_ == 0 {
                                        v_unused_2096_ = crate::leanh::lean_ctor_get(v_l_1775_, 4);
                                        crate::leanh::lean_dec(v_unused_2096_);
                                        v_unused_2097_ = crate::leanh::lean_ctor_get(v_l_1775_, 3);
                                        crate::leanh::lean_dec(v_unused_2097_);
                                        v_unused_2098_ = crate::leanh::lean_ctor_get(v_l_1775_, 2);
                                        crate::leanh::lean_dec(v_unused_2098_);
                                        v_unused_2099_ = crate::leanh::lean_ctor_get(v_l_1775_, 1);
                                        crate::leanh::lean_dec(v_unused_2099_);
                                        v_unused_2100_ = crate::leanh::lean_ctor_get(v_l_1775_, 0);
                                        crate::leanh::lean_dec(v_unused_2100_);
                                        v___x_1961_ = v_l_1775_;
                                        v_isShared_1962_ = v_isSharedCheck_2095_;
                                        state = 27;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_1775_);
                                        v___x_1961_ = crate::leanh::lean_box(0);
                                        v_isShared_1962_ = v_isSharedCheck_2095_;
                                        state = 27;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_r_1957_);
                                    crate::leanh::lean_inc(v_v_1955_);
                                    crate::leanh::lean_inc(v_k_1954_);
                                    v_isSharedCheck_2253_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_1776_)) as u8;
                                    if v_isSharedCheck_2253_ == 0 {
                                        v_unused_2254_ = crate::leanh::lean_ctor_get(v_r_1776_, 4);
                                        crate::leanh::lean_dec(v_unused_2254_);
                                        v_unused_2255_ = crate::leanh::lean_ctor_get(v_r_1776_, 3);
                                        crate::leanh::lean_dec(v_unused_2255_);
                                        v_unused_2256_ = crate::leanh::lean_ctor_get(v_r_1776_, 2);
                                        crate::leanh::lean_dec(v_unused_2256_);
                                        v_unused_2257_ = crate::leanh::lean_ctor_get(v_r_1776_, 1);
                                        crate::leanh::lean_dec(v_unused_2257_);
                                        v_unused_2258_ = crate::leanh::lean_ctor_get(v_r_1776_, 0);
                                        crate::leanh::lean_dec(v_unused_2258_);
                                        v___x_2102_ = v_r_1776_;
                                        v_isShared_2103_ = v_isSharedCheck_2253_;
                                        state = 49;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_r_1776_);
                                        v___x_2102_ = crate::leanh::lean_box(0);
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
                    v___x_2260_ = crate::leanh::lean_unsigned_to_nat(1);
                    if crate::leanh::lean_obj_tag(v_impl_2259_) == 0 {
                        if crate::leanh::lean_obj_tag(v_r_1776_) == 0 {
                            v_size_2261_ = crate::leanh::lean_ctor_get(v_impl_2259_, 0);
                            crate::leanh::lean_inc(v_size_2261_);
                            v_size_2262_ = crate::leanh::lean_ctor_get(v_r_1776_, 0);
                            v_k_2263_ = crate::leanh::lean_ctor_get(v_r_1776_, 1);
                            v_v_2264_ = crate::leanh::lean_ctor_get(v_r_1776_, 2);
                            v_l_2265_ = crate::leanh::lean_ctor_get(v_r_1776_, 3);
                            crate::leanh::lean_inc(v_l_2265_);
                            v_r_2266_ = crate::leanh::lean_ctor_get(v_r_1776_, 4);
                            v___x_2267_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_2268_ = lean_nat_mul(v___x_2267_, v_size_2261_);
                            v___x_2269_ = lean_nat_dec_lt(v___x_2268_, v_size_2262_);
                            crate::leanh::lean_dec(v___x_2268_);
                            if v___x_2269_ == 0 {
                                crate::leanh::lean_dec(v_l_2265_);
                                v___x_2270_ = lean_nat_add(v___x_2260_, v_size_2261_);
                                crate::leanh::lean_dec(v_size_2261_);
                                v___x_2271_ = lean_nat_add(v___x_2270_, v_size_2262_);
                                crate::leanh::lean_dec(v___x_2270_);
                                if v_isShared_1779_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1778_, 3, v_impl_2259_);
                                    crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_2271_);
                                    v___x_2273_ = v___x_1778_;
                                    state = 72;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2274_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2274_,
                                        0,
                                        v___x_2271_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2274_,
                                        1,
                                        v_k_1773_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2274_,
                                        2,
                                        v_v_1774_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2274_,
                                        3,
                                        v_impl_2259_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2274_,
                                        4,
                                        v_r_1776_,
                                    );
                                    v___x_2273_ = v_reuseFailAlloc_2274_;
                                    state = 72;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_inc(v_r_2266_);
                                crate::leanh::lean_inc(v_v_2264_);
                                crate::leanh::lean_inc(v_k_2263_);
                                crate::leanh::lean_inc(v_size_2262_);
                                v_isSharedCheck_2338_ =
                                    (!crate::leanh::lean_is_exclusive(v_r_1776_)) as u8;
                                if v_isSharedCheck_2338_ == 0 {
                                    v_unused_2339_ = crate::leanh::lean_ctor_get(v_r_1776_, 4);
                                    crate::leanh::lean_dec(v_unused_2339_);
                                    v_unused_2340_ = crate::leanh::lean_ctor_get(v_r_1776_, 3);
                                    crate::leanh::lean_dec(v_unused_2340_);
                                    v_unused_2341_ = crate::leanh::lean_ctor_get(v_r_1776_, 2);
                                    crate::leanh::lean_dec(v_unused_2341_);
                                    v_unused_2342_ = crate::leanh::lean_ctor_get(v_r_1776_, 1);
                                    crate::leanh::lean_dec(v_unused_2342_);
                                    v_unused_2343_ = crate::leanh::lean_ctor_get(v_r_1776_, 0);
                                    crate::leanh::lean_dec(v_unused_2343_);
                                    v___x_2276_ = v_r_1776_;
                                    v_isShared_2277_ = v_isSharedCheck_2338_;
                                    state = 73;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_r_1776_);
                                    v___x_2276_ = crate::leanh::lean_box(0);
                                    v_isShared_2277_ = v_isSharedCheck_2338_;
                                    state = 73;
                                    continue;
                                }
                            }
                        } else {
                            v_size_2344_ = crate::leanh::lean_ctor_get(v_impl_2259_, 0);
                            crate::leanh::lean_inc(v_size_2344_);
                            v___x_2345_ = lean_nat_add(v___x_2260_, v_size_2344_);
                            crate::leanh::lean_dec(v_size_2344_);
                            if v_isShared_1779_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1778_, 3, v_impl_2259_);
                                crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_2345_);
                                v___x_2347_ = v___x_1778_;
                                state = 83;
                                continue;
                            } else {
                                v_reuseFailAlloc_2348_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_k_1773_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 2, v_v_1774_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2348_,
                                    3,
                                    v_impl_2259_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 4, v_r_1776_);
                                v___x_2347_ = v_reuseFailAlloc_2348_;
                                state = 83;
                                continue;
                            }
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_r_1776_) == 0 {
                            v_l_2349_ = crate::leanh::lean_ctor_get(v_r_1776_, 3);
                            crate::leanh::lean_inc(v_l_2349_);
                            if crate::leanh::lean_obj_tag(v_l_2349_) == 0 {
                                v_r_2350_ = crate::leanh::lean_ctor_get(v_r_1776_, 4);
                                crate::leanh::lean_inc(v_r_2350_);
                                if crate::leanh::lean_obj_tag(v_r_2350_) == 0 {
                                    v_size_2351_ = crate::leanh::lean_ctor_get(v_r_1776_, 0);
                                    v_k_2352_ = crate::leanh::lean_ctor_get(v_r_1776_, 1);
                                    v_v_2353_ = crate::leanh::lean_ctor_get(v_r_1776_, 2);
                                    v_isSharedCheck_2366_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_1776_)) as u8;
                                    if v_isSharedCheck_2366_ == 0 {
                                        v_unused_2367_ = crate::leanh::lean_ctor_get(v_r_1776_, 4);
                                        crate::leanh::lean_dec(v_unused_2367_);
                                        v_unused_2368_ = crate::leanh::lean_ctor_get(v_r_1776_, 3);
                                        crate::leanh::lean_dec(v_unused_2368_);
                                        v___x_2355_ = v_r_1776_;
                                        v_isShared_2356_ = v_isSharedCheck_2366_;
                                        state = 84;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_2353_);
                                        crate::leanh::lean_inc(v_k_2352_);
                                        crate::leanh::lean_inc(v_size_2351_);
                                        crate::leanh::lean_dec(v_r_1776_);
                                        v___x_2355_ = crate::leanh::lean_box(0);
                                        v_isShared_2356_ = v_isSharedCheck_2366_;
                                        state = 84;
                                        continue;
                                    }
                                } else {
                                    v_k_2369_ = crate::leanh::lean_ctor_get(v_r_1776_, 1);
                                    v_v_2370_ = crate::leanh::lean_ctor_get(v_r_1776_, 2);
                                    v_isSharedCheck_2393_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_1776_)) as u8;
                                    if v_isSharedCheck_2393_ == 0 {
                                        v_unused_2394_ = crate::leanh::lean_ctor_get(v_r_1776_, 4);
                                        crate::leanh::lean_dec(v_unused_2394_);
                                        v_unused_2395_ = crate::leanh::lean_ctor_get(v_r_1776_, 3);
                                        crate::leanh::lean_dec(v_unused_2395_);
                                        v_unused_2396_ = crate::leanh::lean_ctor_get(v_r_1776_, 0);
                                        crate::leanh::lean_dec(v_unused_2396_);
                                        v___x_2372_ = v_r_1776_;
                                        v_isShared_2373_ = v_isSharedCheck_2393_;
                                        state = 87;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_2370_);
                                        crate::leanh::lean_inc(v_k_2369_);
                                        crate::leanh::lean_dec(v_r_1776_);
                                        v___x_2372_ = crate::leanh::lean_box(0);
                                        v_isShared_2373_ = v_isSharedCheck_2393_;
                                        state = 87;
                                        continue;
                                    }
                                }
                            } else {
                                v_r_2397_ = crate::leanh::lean_ctor_get(v_r_1776_, 4);
                                crate::leanh::lean_inc(v_r_2397_);
                                if crate::leanh::lean_obj_tag(v_r_2397_) == 0 {
                                    v_k_2398_ = crate::leanh::lean_ctor_get(v_r_1776_, 1);
                                    v_v_2399_ = crate::leanh::lean_ctor_get(v_r_1776_, 2);
                                    v_isSharedCheck_2410_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_1776_)) as u8;
                                    if v_isSharedCheck_2410_ == 0 {
                                        v_unused_2411_ = crate::leanh::lean_ctor_get(v_r_1776_, 4);
                                        crate::leanh::lean_dec(v_unused_2411_);
                                        v_unused_2412_ = crate::leanh::lean_ctor_get(v_r_1776_, 3);
                                        crate::leanh::lean_dec(v_unused_2412_);
                                        v_unused_2413_ = crate::leanh::lean_ctor_get(v_r_1776_, 0);
                                        crate::leanh::lean_dec(v_unused_2413_);
                                        v___x_2401_ = v_r_1776_;
                                        v_isShared_2402_ = v_isSharedCheck_2410_;
                                        state = 92;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_2399_);
                                        crate::leanh::lean_inc(v_k_2398_);
                                        crate::leanh::lean_dec(v_r_1776_);
                                        v___x_2401_ = crate::leanh::lean_box(0);
                                        v_isShared_2402_ = v_isSharedCheck_2410_;
                                        state = 92;
                                        continue;
                                    }
                                } else {
                                    v_size_2414_ = crate::leanh::lean_ctor_get(v_r_1776_, 0);
                                    v_k_2415_ = crate::leanh::lean_ctor_get(v_r_1776_, 1);
                                    v_v_2416_ = crate::leanh::lean_ctor_get(v_r_1776_, 2);
                                    v_isSharedCheck_2427_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_1776_)) as u8;
                                    if v_isSharedCheck_2427_ == 0 {
                                        v_unused_2428_ = crate::leanh::lean_ctor_get(v_r_1776_, 4);
                                        crate::leanh::lean_dec(v_unused_2428_);
                                        v_unused_2429_ = crate::leanh::lean_ctor_get(v_r_1776_, 3);
                                        crate::leanh::lean_dec(v_unused_2429_);
                                        v___x_2418_ = v_r_1776_;
                                        v_isShared_2419_ = v_isSharedCheck_2427_;
                                        state = 95;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_2416_);
                                        crate::leanh::lean_inc(v_k_2415_);
                                        crate::leanh::lean_inc(v_size_2414_);
                                        crate::leanh::lean_dec(v_r_1776_);
                                        v___x_2418_ = crate::leanh::lean_box(0);
                                        v_isShared_2419_ = v_isSharedCheck_2427_;
                                        state = 95;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            if v_isShared_1779_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1778_, 3, v_r_1776_);
                                crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_2260_);
                                v___x_2431_ = v___x_1778_;
                                state = 98;
                                continue;
                            } else {
                                v_reuseFailAlloc_2432_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2260_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_k_1773_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 2, v_v_1774_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 3, v_r_1776_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 4, v_r_1776_);
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
                v_size_1803_ = crate::leanh::lean_ctor_get(v_l_1790_, 0);
                v_size_1804_ = crate::leanh::lean_ctor_get(v_r_1791_, 0);
                v_k_1805_ = crate::leanh::lean_ctor_get(v_r_1791_, 1);
                v_v_1806_ = crate::leanh::lean_ctor_get(v_r_1791_, 2);
                v_l_1807_ = crate::leanh::lean_ctor_get(v_r_1791_, 3);
                v_r_1808_ = crate::leanh::lean_ctor_get(v_r_1791_, 4);
                v___x_1809_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1810_ = lean_nat_mul(v___x_1809_, v_size_1803_);
                v___x_1811_ = lean_nat_dec_lt(v_size_1804_, v___x_1810_);
                crate::leanh::lean_dec(v___x_1810_);
                if v___x_1811_ == 0 {
                    crate::leanh::lean_inc(v_r_1808_);
                    crate::leanh::lean_inc(v_l_1807_);
                    crate::leanh::lean_inc(v_v_1806_);
                    crate::leanh::lean_inc(v_k_1805_);
                    v_isSharedCheck_1840_ = (!crate::leanh::lean_is_exclusive(v_r_1791_)) as u8;
                    if v_isSharedCheck_1840_ == 0 {
                        v_unused_1841_ = crate::leanh::lean_ctor_get(v_r_1791_, 4);
                        crate::leanh::lean_dec(v_unused_1841_);
                        v_unused_1842_ = crate::leanh::lean_ctor_get(v_r_1791_, 3);
                        crate::leanh::lean_dec(v_unused_1842_);
                        v_unused_1843_ = crate::leanh::lean_ctor_get(v_r_1791_, 2);
                        crate::leanh::lean_dec(v_unused_1843_);
                        v_unused_1844_ = crate::leanh::lean_ctor_get(v_r_1791_, 1);
                        crate::leanh::lean_dec(v_unused_1844_);
                        v_unused_1845_ = crate::leanh::lean_ctor_get(v_r_1791_, 0);
                        crate::leanh::lean_dec(v_unused_1845_);
                        v___x_1813_ = v_r_1791_;
                        v_isShared_1814_ = v_isSharedCheck_1840_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_1791_);
                        v___x_1813_ = crate::leanh::lean_box(0);
                        v_isShared_1814_ = v_isSharedCheck_1840_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1778_);
                    v___x_1846_ = lean_nat_add(v___x_1785_, v_size_1787_);
                    crate::leanh::lean_dec(v_size_1787_);
                    v___x_1847_ = lean_nat_add(v___x_1846_, v_size_1786_);
                    crate::leanh::lean_dec(v___x_1846_);
                    v___x_1848_ = lean_nat_add(v___x_1785_, v_size_1786_);
                    crate::leanh::lean_dec(v_size_1786_);
                    v___x_1849_ = lean_nat_add(v___x_1848_, v_size_1804_);
                    crate::leanh::lean_dec(v___x_1848_);
                    crate::leanh::lean_inc_ref(v_impl_1784_);
                    if v_isShared_1802_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1801_, 4, v_impl_1784_);
                        crate::leanh::lean_ctor_set(v___x_1801_, 3, v_r_1791_);
                        crate::leanh::lean_ctor_set(v___x_1801_, 2, v_v_1774_);
                        crate::leanh::lean_ctor_set(v___x_1801_, 1, v_k_1773_);
                        crate::leanh::lean_ctor_set(v___x_1801_, 0, v___x_1849_);
                        v___x_1851_ = v___x_1801_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1864_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1849_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_k_1773_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 2, v_v_1774_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 3, v_r_1791_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 4, v_impl_1784_);
                        v___x_1851_ = v_reuseFailAlloc_1864_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1815_ = lean_nat_add(v___x_1785_, v_size_1787_);
                crate::leanh::lean_dec(v_size_1787_);
                v___x_1816_ = lean_nat_add(v___x_1815_, v_size_1786_);
                crate::leanh::lean_dec(v___x_1815_);
                v___x_1828_ = lean_nat_add(v___x_1785_, v_size_1803_);
                if crate::leanh::lean_obj_tag(v_l_1807_) == 0 {
                    v_size_1838_ = crate::leanh::lean_ctor_get(v_l_1807_, 0);
                    crate::leanh::lean_inc(v_size_1838_);
                    v___y_1830_ = v_size_1838_;
                    state = 8;
                    continue;
                } else {
                    v___x_1839_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1830_ = v___x_1839_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1821_ = lean_nat_add(v___y_1818_, v___y_1820_);
                crate::leanh::lean_dec(v___y_1820_);
                crate::leanh::lean_dec(v___y_1818_);
                if v_isShared_1814_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1813_, 4, v_impl_1784_);
                    crate::leanh::lean_ctor_set(v___x_1813_, 3, v_r_1808_);
                    crate::leanh::lean_ctor_set(v___x_1813_, 2, v_v_1774_);
                    crate::leanh::lean_ctor_set(v___x_1813_, 1, v_k_1773_);
                    crate::leanh::lean_ctor_set(v___x_1813_, 0, v___x_1821_);
                    v___x_1823_ = v___x_1813_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1827_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1821_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_k_1773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_v_1774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_r_1808_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_impl_1784_);
                    v___x_1823_ = v_reuseFailAlloc_1827_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1802_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1801_, 4, v___x_1823_);
                    crate::leanh::lean_ctor_set(v___x_1801_, 3, v___y_1819_);
                    crate::leanh::lean_ctor_set(v___x_1801_, 2, v_v_1806_);
                    crate::leanh::lean_ctor_set(v___x_1801_, 1, v_k_1805_);
                    crate::leanh::lean_ctor_set(v___x_1801_, 0, v___x_1816_);
                    v___x_1825_ = v___x_1801_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1826_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_k_1805_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 2, v_v_1806_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 3, v___y_1819_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 4, v___x_1823_);
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
                crate::leanh::lean_dec(v___y_1830_);
                crate::leanh::lean_dec(v___x_1828_);
                if v_isShared_1779_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1778_, 4, v_l_1807_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 3, v_l_1790_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 2, v_v_1789_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 1, v_k_1788_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_1831_);
                    v___x_1833_ = v___x_1778_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1837_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_k_1788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 2, v_v_1789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 3, v_l_1790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 4, v_l_1807_);
                    v___x_1833_ = v_reuseFailAlloc_1837_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1834_ = lean_nat_add(v___x_1785_, v_size_1786_);
                crate::leanh::lean_dec(v_size_1786_);
                if crate::leanh::lean_obj_tag(v_r_1808_) == 0 {
                    v_size_1835_ = crate::leanh::lean_ctor_get(v_r_1808_, 0);
                    crate::leanh::lean_inc(v_size_1835_);
                    v___y_1818_ = v___x_1834_;
                    v___y_1819_ = v___x_1833_;
                    v___y_1820_ = v_size_1835_;
                    state = 5;
                    continue;
                } else {
                    v___x_1836_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1818_ = v___x_1834_;
                    v___y_1819_ = v___x_1833_;
                    v___y_1820_ = v___x_1836_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1858_ = (!crate::leanh::lean_is_exclusive(v_impl_1784_)) as u8;
                if v_isSharedCheck_1858_ == 0 {
                    v_unused_1859_ = crate::leanh::lean_ctor_get(v_impl_1784_, 4);
                    crate::leanh::lean_dec(v_unused_1859_);
                    v_unused_1860_ = crate::leanh::lean_ctor_get(v_impl_1784_, 3);
                    crate::leanh::lean_dec(v_unused_1860_);
                    v_unused_1861_ = crate::leanh::lean_ctor_get(v_impl_1784_, 2);
                    crate::leanh::lean_dec(v_unused_1861_);
                    v_unused_1862_ = crate::leanh::lean_ctor_get(v_impl_1784_, 1);
                    crate::leanh::lean_dec(v_unused_1862_);
                    v_unused_1863_ = crate::leanh::lean_ctor_get(v_impl_1784_, 0);
                    crate::leanh::lean_dec(v_unused_1863_);
                    v___x_1853_ = v_impl_1784_;
                    v_isShared_1854_ = v_isSharedCheck_1858_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_impl_1784_);
                    v___x_1853_ = crate::leanh::lean_box(0);
                    v_isShared_1854_ = v_isSharedCheck_1858_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1854_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1853_, 4, v___x_1851_);
                    crate::leanh::lean_ctor_set(v___x_1853_, 3, v_l_1790_);
                    crate::leanh::lean_ctor_set(v___x_1853_, 2, v_v_1789_);
                    crate::leanh::lean_ctor_set(v___x_1853_, 1, v_k_1788_);
                    crate::leanh::lean_ctor_set(v___x_1853_, 0, v___x_1847_);
                    v___x_1856_ = v___x_1853_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1847_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_k_1788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_v_1789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_l_1790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 4, v___x_1851_);
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
                v_size_1884_ = crate::leanh::lean_ctor_get(v_r_1877_, 0);
                v___x_1885_ = lean_nat_add(v___x_1785_, v_size_1878_);
                crate::leanh::lean_dec(v_size_1878_);
                v___x_1886_ = lean_nat_add(v___x_1785_, v_size_1884_);
                if v_isShared_1883_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1882_, 4, v_impl_1784_);
                    crate::leanh::lean_ctor_set(v___x_1882_, 3, v_r_1877_);
                    crate::leanh::lean_ctor_set(v___x_1882_, 2, v_v_1774_);
                    crate::leanh::lean_ctor_set(v___x_1882_, 1, v_k_1773_);
                    crate::leanh::lean_ctor_set(v___x_1882_, 0, v___x_1886_);
                    v___x_1888_ = v___x_1882_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1892_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_k_1773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_v_1774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 3, v_r_1877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 4, v_impl_1784_);
                    v___x_1888_ = v_reuseFailAlloc_1892_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1779_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1778_, 4, v___x_1888_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 3, v_l_1876_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 2, v_v_1880_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 1, v_k_1879_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_1885_);
                    v___x_1890_ = v___x_1778_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1891_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_k_1879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1891_, 2, v_v_1880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1891_, 3, v_l_1876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1891_, 4, v___x_1888_);
                    v___x_1890_ = v_reuseFailAlloc_1891_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1890_;
            }
            17 => {
                v___x_1901_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_1900_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1899_, 3, v_r_1877_);
                    crate::leanh::lean_ctor_set(v___x_1899_, 2, v_v_1774_);
                    crate::leanh::lean_ctor_set(v___x_1899_, 1, v_k_1773_);
                    crate::leanh::lean_ctor_set(v___x_1899_, 0, v___x_1785_);
                    v___x_1903_ = v___x_1899_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1907_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_k_1773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 2, v_v_1774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 3, v_r_1877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 4, v_r_1877_);
                    v___x_1903_ = v_reuseFailAlloc_1907_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1779_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1778_, 4, v___x_1903_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 3, v_l_1876_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 2, v_v_1897_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 1, v_k_1896_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_1901_);
                    v___x_1905_ = v___x_1778_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1906_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_k_1896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 2, v_v_1897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 3, v_l_1876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 4, v___x_1903_);
                    v___x_1905_ = v_reuseFailAlloc_1906_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1905_;
            }
            20 => {
                v_k_1918_ = crate::leanh::lean_ctor_get(v_r_1912_, 1);
                v_v_1919_ = crate::leanh::lean_ctor_get(v_r_1912_, 2);
                v_isSharedCheck_1933_ = (!crate::leanh::lean_is_exclusive(v_r_1912_)) as u8;
                if v_isSharedCheck_1933_ == 0 {
                    v_unused_1934_ = crate::leanh::lean_ctor_get(v_r_1912_, 4);
                    crate::leanh::lean_dec(v_unused_1934_);
                    v_unused_1935_ = crate::leanh::lean_ctor_get(v_r_1912_, 3);
                    crate::leanh::lean_dec(v_unused_1935_);
                    v_unused_1936_ = crate::leanh::lean_ctor_get(v_r_1912_, 0);
                    crate::leanh::lean_dec(v_unused_1936_);
                    v___x_1921_ = v_r_1912_;
                    v_isShared_1922_ = v_isSharedCheck_1933_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1919_);
                    crate::leanh::lean_inc(v_k_1918_);
                    crate::leanh::lean_dec(v_r_1912_);
                    v___x_1921_ = crate::leanh::lean_box(0);
                    v_isShared_1922_ = v_isSharedCheck_1933_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_1923_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_1922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1921_, 4, v_l_1876_);
                    crate::leanh::lean_ctor_set(v___x_1921_, 3, v_l_1876_);
                    crate::leanh::lean_ctor_set(v___x_1921_, 2, v_v_1914_);
                    crate::leanh::lean_ctor_set(v___x_1921_, 1, v_k_1913_);
                    crate::leanh::lean_ctor_set(v___x_1921_, 0, v___x_1785_);
                    v___x_1925_ = v___x_1921_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1932_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_k_1913_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 2, v_v_1914_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 3, v_l_1876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 4, v_l_1876_);
                    v___x_1925_ = v_reuseFailAlloc_1932_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_1917_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1916_, 4, v_l_1876_);
                    crate::leanh::lean_ctor_set(v___x_1916_, 2, v_v_1774_);
                    crate::leanh::lean_ctor_set(v___x_1916_, 1, v_k_1773_);
                    crate::leanh::lean_ctor_set(v___x_1916_, 0, v___x_1785_);
                    v___x_1927_ = v___x_1916_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1931_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_k_1773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_v_1774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_l_1876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_l_1876_);
                    v___x_1927_ = v_reuseFailAlloc_1931_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_1779_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1778_, 4, v___x_1927_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 3, v___x_1925_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 2, v_v_1919_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 1, v_k_1918_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_1923_);
                    v___x_1929_ = v___x_1778_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1930_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_k_1918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_v_1919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 3, v___x_1925_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 4, v___x_1927_);
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
                v_tree_1964_ = crate::leanh::lean_ctor_get(v___x_1963_, 2);
                crate::leanh::lean_inc(v_tree_1964_);
                if crate::leanh::lean_obj_tag(v_tree_1964_) == 0 {
                    v_k_1965_ = crate::leanh::lean_ctor_get(v___x_1963_, 0);
                    crate::leanh::lean_inc(v_k_1965_);
                    v_v_1966_ = crate::leanh::lean_ctor_get(v___x_1963_, 1);
                    crate::leanh::lean_inc(v_v_1966_);
                    crate::leanh::lean_dec_ref(v___x_1963_);
                    v_size_1967_ = crate::leanh::lean_ctor_get(v_tree_1964_, 0);
                    v___x_1968_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1969_ = lean_nat_mul(v___x_1968_, v_size_1967_);
                    v___x_1970_ = lean_nat_dec_lt(v___x_1969_, v_size_1953_);
                    crate::leanh::lean_dec(v___x_1969_);
                    if v___x_1970_ == 0 {
                        crate::leanh::lean_dec(v_l_1956_);
                        v___x_1971_ = lean_nat_add(v___x_1958_, v_size_1967_);
                        v___x_1972_ = lean_nat_add(v___x_1971_, v_size_1953_);
                        crate::leanh::lean_dec(v___x_1971_);
                        if v_isShared_1962_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1961_, 4, v_r_1776_);
                            crate::leanh::lean_ctor_set(v___x_1961_, 3, v_tree_1964_);
                            crate::leanh::lean_ctor_set(v___x_1961_, 2, v_v_1966_);
                            crate::leanh::lean_ctor_set(v___x_1961_, 1, v_k_1965_);
                            crate::leanh::lean_ctor_set(v___x_1961_, 0, v___x_1972_);
                            v___x_1974_ = v___x_1961_;
                            state = 28;
                            continue;
                        } else {
                            v_reuseFailAlloc_1975_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_k_1965_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1975_, 2, v_v_1966_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1975_, 3, v_tree_1964_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1975_, 4, v_r_1776_);
                            v___x_1974_ = v_reuseFailAlloc_1975_;
                            state = 28;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_r_1957_);
                        crate::leanh::lean_inc(v_v_1955_);
                        crate::leanh::lean_inc(v_k_1954_);
                        crate::leanh::lean_inc(v_size_1953_);
                        v_isSharedCheck_2030_ = (!crate::leanh::lean_is_exclusive(v_r_1776_)) as u8;
                        if v_isSharedCheck_2030_ == 0 {
                            v_unused_2031_ = crate::leanh::lean_ctor_get(v_r_1776_, 4);
                            crate::leanh::lean_dec(v_unused_2031_);
                            v_unused_2032_ = crate::leanh::lean_ctor_get(v_r_1776_, 3);
                            crate::leanh::lean_dec(v_unused_2032_);
                            v_unused_2033_ = crate::leanh::lean_ctor_get(v_r_1776_, 2);
                            crate::leanh::lean_dec(v_unused_2033_);
                            v_unused_2034_ = crate::leanh::lean_ctor_get(v_r_1776_, 1);
                            crate::leanh::lean_dec(v_unused_2034_);
                            v_unused_2035_ = crate::leanh::lean_ctor_get(v_r_1776_, 0);
                            crate::leanh::lean_dec(v_unused_2035_);
                            v___x_1977_ = v_r_1776_;
                            v_isShared_1978_ = v_isSharedCheck_2030_;
                            state = 29;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_r_1776_);
                            v___x_1977_ = crate::leanh::lean_box(0);
                            v_isShared_1978_ = v_isSharedCheck_2030_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_r_1957_);
                    crate::leanh::lean_inc(v_v_1955_);
                    crate::leanh::lean_inc(v_k_1954_);
                    crate::leanh::lean_inc(v_size_1953_);
                    v_isSharedCheck_2089_ = (!crate::leanh::lean_is_exclusive(v_r_1776_)) as u8;
                    if v_isSharedCheck_2089_ == 0 {
                        v_unused_2090_ = crate::leanh::lean_ctor_get(v_r_1776_, 4);
                        crate::leanh::lean_dec(v_unused_2090_);
                        v_unused_2091_ = crate::leanh::lean_ctor_get(v_r_1776_, 3);
                        crate::leanh::lean_dec(v_unused_2091_);
                        v_unused_2092_ = crate::leanh::lean_ctor_get(v_r_1776_, 2);
                        crate::leanh::lean_dec(v_unused_2092_);
                        v_unused_2093_ = crate::leanh::lean_ctor_get(v_r_1776_, 1);
                        crate::leanh::lean_dec(v_unused_2093_);
                        v_unused_2094_ = crate::leanh::lean_ctor_get(v_r_1776_, 0);
                        crate::leanh::lean_dec(v_unused_2094_);
                        v___x_2037_ = v_r_1776_;
                        v_isShared_2038_ = v_isSharedCheck_2089_;
                        state = 38;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_1776_);
                        v___x_2037_ = crate::leanh::lean_box(0);
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
                v_size_1979_ = crate::leanh::lean_ctor_get(v_l_1956_, 0);
                v_k_1980_ = crate::leanh::lean_ctor_get(v_l_1956_, 1);
                v_v_1981_ = crate::leanh::lean_ctor_get(v_l_1956_, 2);
                v_l_1982_ = crate::leanh::lean_ctor_get(v_l_1956_, 3);
                v_r_1983_ = crate::leanh::lean_ctor_get(v_l_1956_, 4);
                v_size_1984_ = crate::leanh::lean_ctor_get(v_r_1957_, 0);
                v___x_1985_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1986_ = lean_nat_mul(v___x_1985_, v_size_1984_);
                v___x_1987_ = lean_nat_dec_lt(v_size_1979_, v___x_1986_);
                crate::leanh::lean_dec(v___x_1986_);
                if v___x_1987_ == 0 {
                    crate::leanh::lean_inc(v_r_1983_);
                    crate::leanh::lean_inc(v_l_1982_);
                    crate::leanh::lean_inc(v_v_1981_);
                    crate::leanh::lean_inc(v_k_1980_);
                    v_isSharedCheck_2015_ = (!crate::leanh::lean_is_exclusive(v_l_1956_)) as u8;
                    if v_isSharedCheck_2015_ == 0 {
                        v_unused_2016_ = crate::leanh::lean_ctor_get(v_l_1956_, 4);
                        crate::leanh::lean_dec(v_unused_2016_);
                        v_unused_2017_ = crate::leanh::lean_ctor_get(v_l_1956_, 3);
                        crate::leanh::lean_dec(v_unused_2017_);
                        v_unused_2018_ = crate::leanh::lean_ctor_get(v_l_1956_, 2);
                        crate::leanh::lean_dec(v_unused_2018_);
                        v_unused_2019_ = crate::leanh::lean_ctor_get(v_l_1956_, 1);
                        crate::leanh::lean_dec(v_unused_2019_);
                        v_unused_2020_ = crate::leanh::lean_ctor_get(v_l_1956_, 0);
                        crate::leanh::lean_dec(v_unused_2020_);
                        v___x_1989_ = v_l_1956_;
                        v_isShared_1990_ = v_isSharedCheck_2015_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_1956_);
                        v___x_1989_ = crate::leanh::lean_box(0);
                        v_isShared_1990_ = v_isSharedCheck_2015_;
                        state = 30;
                        continue;
                    }
                } else {
                    v___x_2021_ = lean_nat_add(v___x_1958_, v_size_1967_);
                    v___x_2022_ = lean_nat_add(v___x_2021_, v_size_1953_);
                    crate::leanh::lean_dec(v_size_1953_);
                    v___x_2023_ = lean_nat_add(v___x_2021_, v_size_1979_);
                    crate::leanh::lean_dec(v___x_2021_);
                    if v_isShared_1978_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1977_, 4, v_l_1956_);
                        crate::leanh::lean_ctor_set(v___x_1977_, 3, v_tree_1964_);
                        crate::leanh::lean_ctor_set(v___x_1977_, 2, v_v_1966_);
                        crate::leanh::lean_ctor_set(v___x_1977_, 1, v_k_1965_);
                        crate::leanh::lean_ctor_set(v___x_1977_, 0, v___x_2023_);
                        v___x_2025_ = v___x_1977_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_2029_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2023_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_k_1965_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 2, v_v_1966_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 3, v_tree_1964_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 4, v_l_1956_);
                        v___x_2025_ = v_reuseFailAlloc_2029_;
                        state = 36;
                        continue;
                    }
                }
            }
            30 => {
                v___x_1991_ = lean_nat_add(v___x_1958_, v_size_1967_);
                v___x_1992_ = lean_nat_add(v___x_1991_, v_size_1953_);
                crate::leanh::lean_dec(v_size_1953_);
                if crate::leanh::lean_obj_tag(v_l_1982_) == 0 {
                    v_size_2013_ = crate::leanh::lean_ctor_get(v_l_1982_, 0);
                    crate::leanh::lean_inc(v_size_2013_);
                    v___y_2005_ = v_size_2013_;
                    state = 34;
                    continue;
                } else {
                    v___x_2014_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2005_ = v___x_2014_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_1997_ = lean_nat_add(v___y_1995_, v___y_1996_);
                crate::leanh::lean_dec(v___y_1996_);
                crate::leanh::lean_dec(v___y_1995_);
                if v_isShared_1990_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1989_, 4, v_r_1957_);
                    crate::leanh::lean_ctor_set(v___x_1989_, 3, v_r_1983_);
                    crate::leanh::lean_ctor_set(v___x_1989_, 2, v_v_1955_);
                    crate::leanh::lean_ctor_set(v___x_1989_, 1, v_k_1954_);
                    crate::leanh::lean_ctor_set(v___x_1989_, 0, v___x_1997_);
                    v___x_1999_ = v___x_1989_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1997_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_k_1954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_v_1955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_r_1983_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 4, v_r_1957_);
                    v___x_1999_ = v_reuseFailAlloc_2003_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1978_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1977_, 4, v___x_1999_);
                    crate::leanh::lean_ctor_set(v___x_1977_, 3, v___y_1994_);
                    crate::leanh::lean_ctor_set(v___x_1977_, 2, v_v_1981_);
                    crate::leanh::lean_ctor_set(v___x_1977_, 1, v_k_1980_);
                    crate::leanh::lean_ctor_set(v___x_1977_, 0, v___x_1992_);
                    v___x_2001_ = v___x_1977_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2002_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1992_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_k_1980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_v_1981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 3, v___y_1994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 4, v___x_1999_);
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
                crate::leanh::lean_dec(v___y_2005_);
                crate::leanh::lean_dec(v___x_1991_);
                if v_isShared_1962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1961_, 4, v_l_1982_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 3, v_tree_1964_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 2, v_v_1966_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 1, v_k_1965_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 0, v___x_2006_);
                    v___x_2008_ = v___x_1961_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2012_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_k_1965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_v_1966_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 3, v_tree_1964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 4, v_l_1982_);
                    v___x_2008_ = v_reuseFailAlloc_2012_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_2009_ = lean_nat_add(v___x_1958_, v_size_1984_);
                if crate::leanh::lean_obj_tag(v_r_1983_) == 0 {
                    v_size_2010_ = crate::leanh::lean_ctor_get(v_r_1983_, 0);
                    crate::leanh::lean_inc(v_size_2010_);
                    v___y_1994_ = v___x_2008_;
                    v___y_1995_ = v___x_2009_;
                    v___y_1996_ = v_size_2010_;
                    state = 31;
                    continue;
                } else {
                    v___x_2011_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1994_ = v___x_2008_;
                    v___y_1995_ = v___x_2009_;
                    v___y_1996_ = v___x_2011_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                if v_isShared_1962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1961_, 4, v_r_1957_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 3, v___x_2025_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 2, v_v_1955_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 1, v_k_1954_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 0, v___x_2022_);
                    v___x_2027_ = v___x_1961_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2028_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_k_1954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2028_, 2, v_v_1955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2028_, 3, v___x_2025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2028_, 4, v_r_1957_);
                    v___x_2027_ = v_reuseFailAlloc_2028_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_2027_;
            }
            38 => {
                if crate::leanh::lean_obj_tag(v_l_1956_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_1957_) == 0 {
                        v_k_2039_ = crate::leanh::lean_ctor_get(v___x_1963_, 0);
                        crate::leanh::lean_inc(v_k_2039_);
                        v_v_2040_ = crate::leanh::lean_ctor_get(v___x_1963_, 1);
                        crate::leanh::lean_inc(v_v_2040_);
                        crate::leanh::lean_dec_ref(v___x_1963_);
                        v_size_2041_ = crate::leanh::lean_ctor_get(v_l_1956_, 0);
                        v___x_2042_ = lean_nat_add(v___x_1958_, v_size_1953_);
                        crate::leanh::lean_dec(v_size_1953_);
                        v___x_2043_ = lean_nat_add(v___x_1958_, v_size_2041_);
                        if v_isShared_2038_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2037_, 4, v_l_1956_);
                            crate::leanh::lean_ctor_set(v___x_2037_, 3, v_tree_1964_);
                            crate::leanh::lean_ctor_set(v___x_2037_, 2, v_v_2040_);
                            crate::leanh::lean_ctor_set(v___x_2037_, 1, v_k_2039_);
                            crate::leanh::lean_ctor_set(v___x_2037_, 0, v___x_2043_);
                            v___x_2045_ = v___x_2037_;
                            state = 39;
                            continue;
                        } else {
                            v_reuseFailAlloc_2049_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2043_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_k_2039_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_v_2040_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 3, v_tree_1964_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 4, v_l_1956_);
                            v___x_2045_ = v_reuseFailAlloc_2049_;
                            state = 39;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_size_1953_);
                        v_k_2050_ = crate::leanh::lean_ctor_get(v___x_1963_, 0);
                        crate::leanh::lean_inc(v_k_2050_);
                        v_v_2051_ = crate::leanh::lean_ctor_get(v___x_1963_, 1);
                        crate::leanh::lean_inc(v_v_2051_);
                        crate::leanh::lean_dec_ref(v___x_1963_);
                        v_k_2052_ = crate::leanh::lean_ctor_get(v_l_1956_, 1);
                        v_v_2053_ = crate::leanh::lean_ctor_get(v_l_1956_, 2);
                        v_isSharedCheck_2067_ = (!crate::leanh::lean_is_exclusive(v_l_1956_)) as u8;
                        if v_isSharedCheck_2067_ == 0 {
                            v_unused_2068_ = crate::leanh::lean_ctor_get(v_l_1956_, 4);
                            crate::leanh::lean_dec(v_unused_2068_);
                            v_unused_2069_ = crate::leanh::lean_ctor_get(v_l_1956_, 3);
                            crate::leanh::lean_dec(v_unused_2069_);
                            v_unused_2070_ = crate::leanh::lean_ctor_get(v_l_1956_, 0);
                            crate::leanh::lean_dec(v_unused_2070_);
                            v___x_2055_ = v_l_1956_;
                            v_isShared_2056_ = v_isSharedCheck_2067_;
                            state = 41;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_v_2053_);
                            crate::leanh::lean_inc(v_k_2052_);
                            crate::leanh::lean_dec(v_l_1956_);
                            v___x_2055_ = crate::leanh::lean_box(0);
                            v_isShared_2056_ = v_isSharedCheck_2067_;
                            state = 41;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_r_1957_) == 0 {
                        crate::leanh::lean_dec(v_size_1953_);
                        v_k_2071_ = crate::leanh::lean_ctor_get(v___x_1963_, 0);
                        crate::leanh::lean_inc(v_k_2071_);
                        v_v_2072_ = crate::leanh::lean_ctor_get(v___x_1963_, 1);
                        crate::leanh::lean_inc(v_v_2072_);
                        crate::leanh::lean_dec_ref(v___x_1963_);
                        v___x_2073_ = crate::leanh::lean_unsigned_to_nat(3);
                        if v_isShared_2038_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2037_, 4, v_l_1956_);
                            crate::leanh::lean_ctor_set(v___x_2037_, 2, v_v_2072_);
                            crate::leanh::lean_ctor_set(v___x_2037_, 1, v_k_2071_);
                            crate::leanh::lean_ctor_set(v___x_2037_, 0, v___x_1958_);
                            v___x_2075_ = v___x_2037_;
                            state = 45;
                            continue;
                        } else {
                            v_reuseFailAlloc_2079_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_1958_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_k_2071_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_v_2072_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_l_1956_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 4, v_l_1956_);
                            v___x_2075_ = v_reuseFailAlloc_2079_;
                            state = 45;
                            continue;
                        }
                    } else {
                        v_k_2080_ = crate::leanh::lean_ctor_get(v___x_1963_, 0);
                        crate::leanh::lean_inc(v_k_2080_);
                        v_v_2081_ = crate::leanh::lean_ctor_get(v___x_1963_, 1);
                        crate::leanh::lean_inc(v_v_2081_);
                        crate::leanh::lean_dec_ref(v___x_1963_);
                        if v_isShared_2038_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2037_, 3, v_r_1957_);
                            v___x_2083_ = v___x_2037_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_2088_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_size_1953_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_k_1954_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 2, v_v_1955_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 3, v_r_1957_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 4, v_r_1957_);
                            v___x_2083_ = v_reuseFailAlloc_2088_;
                            state = 47;
                            continue;
                        }
                    }
                }
            }
            39 => {
                if v_isShared_1962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1961_, 4, v_r_1957_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 3, v___x_2045_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 2, v_v_1955_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 1, v_k_1954_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 0, v___x_2042_);
                    v___x_2047_ = v___x_1961_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2048_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2042_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_k_1954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_v_1955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 3, v___x_2045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 4, v_r_1957_);
                    v___x_2047_ = v_reuseFailAlloc_2048_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_2047_;
            }
            41 => {
                v___x_2057_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2056_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2055_, 4, v_r_1957_);
                    crate::leanh::lean_ctor_set(v___x_2055_, 3, v_r_1957_);
                    crate::leanh::lean_ctor_set(v___x_2055_, 2, v_v_2051_);
                    crate::leanh::lean_ctor_set(v___x_2055_, 1, v_k_2050_);
                    crate::leanh::lean_ctor_set(v___x_2055_, 0, v___x_1958_);
                    v___x_2059_ = v___x_2055_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2066_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_1958_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_k_2050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 2, v_v_2051_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 3, v_r_1957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 4, v_r_1957_);
                    v___x_2059_ = v_reuseFailAlloc_2066_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                if v_isShared_2038_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2037_, 3, v_r_1957_);
                    crate::leanh::lean_ctor_set(v___x_2037_, 0, v___x_1958_);
                    v___x_2061_ = v___x_2037_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_2065_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_1958_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_k_1954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 2, v_v_1955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 3, v_r_1957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 4, v_r_1957_);
                    v___x_2061_ = v_reuseFailAlloc_2065_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                if v_isShared_1962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1961_, 4, v___x_2061_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 3, v___x_2059_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 2, v_v_2053_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 1, v_k_2052_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 0, v___x_2057_);
                    v___x_2063_ = v___x_1961_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2064_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2057_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_k_2052_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 2, v_v_2053_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 3, v___x_2059_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 4, v___x_2061_);
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
                    crate::leanh::lean_ctor_set(v___x_1961_, 4, v_r_1957_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 3, v___x_2075_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 2, v_v_1955_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 1, v_k_1954_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 0, v___x_2073_);
                    v___x_2077_ = v___x_1961_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2078_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_k_1954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 2, v_v_1955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 3, v___x_2075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 4, v_r_1957_);
                    v___x_2077_ = v_reuseFailAlloc_2078_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_2077_;
            }
            47 => {
                v___x_2084_ = crate::leanh::lean_unsigned_to_nat(2);
                if v_isShared_1962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1961_, 4, v___x_2083_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 3, v_r_1957_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 2, v_v_2081_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 1, v_k_2080_);
                    crate::leanh::lean_ctor_set(v___x_1961_, 0, v___x_2084_);
                    v___x_2086_ = v___x_1961_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_2087_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_k_2080_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_v_2081_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 3, v_r_1957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 4, v___x_2083_);
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
                v_tree_2105_ = crate::leanh::lean_ctor_get(v___x_2104_, 2);
                crate::leanh::lean_inc(v_tree_2105_);
                if crate::leanh::lean_obj_tag(v_tree_2105_) == 0 {
                    v_k_2106_ = crate::leanh::lean_ctor_get(v___x_2104_, 0);
                    crate::leanh::lean_inc(v_k_2106_);
                    v_v_2107_ = crate::leanh::lean_ctor_get(v___x_2104_, 1);
                    crate::leanh::lean_inc(v_v_2107_);
                    crate::leanh::lean_dec_ref(v___x_2104_);
                    v_size_2108_ = crate::leanh::lean_ctor_get(v_tree_2105_, 0);
                    v___x_2109_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2110_ = lean_nat_mul(v___x_2109_, v_size_2108_);
                    v___x_2111_ = lean_nat_dec_lt(v___x_2110_, v_size_1948_);
                    crate::leanh::lean_dec(v___x_2110_);
                    if v___x_2111_ == 0 {
                        crate::leanh::lean_dec(v_r_1952_);
                        v___x_2112_ = lean_nat_add(v___x_1958_, v_size_1948_);
                        v___x_2113_ = lean_nat_add(v___x_2112_, v_size_2108_);
                        crate::leanh::lean_dec(v___x_2112_);
                        if v_isShared_2103_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2102_, 4, v_tree_2105_);
                            crate::leanh::lean_ctor_set(v___x_2102_, 3, v_l_1775_);
                            crate::leanh::lean_ctor_set(v___x_2102_, 2, v_v_2107_);
                            crate::leanh::lean_ctor_set(v___x_2102_, 1, v_k_2106_);
                            crate::leanh::lean_ctor_set(v___x_2102_, 0, v___x_2113_);
                            v___x_2115_ = v___x_2102_;
                            state = 50;
                            continue;
                        } else {
                            v_reuseFailAlloc_2116_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_k_2106_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_v_2107_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 3, v_l_1775_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 4, v_tree_2105_);
                            v___x_2115_ = v_reuseFailAlloc_2116_;
                            state = 50;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_l_1951_);
                        crate::leanh::lean_inc(v_v_1950_);
                        crate::leanh::lean_inc(v_k_1949_);
                        crate::leanh::lean_inc(v_size_1948_);
                        v_isSharedCheck_2182_ = (!crate::leanh::lean_is_exclusive(v_l_1775_)) as u8;
                        if v_isSharedCheck_2182_ == 0 {
                            v_unused_2183_ = crate::leanh::lean_ctor_get(v_l_1775_, 4);
                            crate::leanh::lean_dec(v_unused_2183_);
                            v_unused_2184_ = crate::leanh::lean_ctor_get(v_l_1775_, 3);
                            crate::leanh::lean_dec(v_unused_2184_);
                            v_unused_2185_ = crate::leanh::lean_ctor_get(v_l_1775_, 2);
                            crate::leanh::lean_dec(v_unused_2185_);
                            v_unused_2186_ = crate::leanh::lean_ctor_get(v_l_1775_, 1);
                            crate::leanh::lean_dec(v_unused_2186_);
                            v_unused_2187_ = crate::leanh::lean_ctor_get(v_l_1775_, 0);
                            crate::leanh::lean_dec(v_unused_2187_);
                            v___x_2118_ = v_l_1775_;
                            v_isShared_2119_ = v_isSharedCheck_2182_;
                            state = 51;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_1775_);
                            v___x_2118_ = crate::leanh::lean_box(0);
                            v_isShared_2119_ = v_isSharedCheck_2182_;
                            state = 51;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_l_1951_) == 0 {
                        crate::leanh::lean_inc_ref(v_l_1951_);
                        crate::leanh::lean_inc(v_v_1950_);
                        crate::leanh::lean_inc(v_k_1949_);
                        crate::leanh::lean_inc(v_size_1948_);
                        v_isSharedCheck_2211_ = (!crate::leanh::lean_is_exclusive(v_l_1775_)) as u8;
                        if v_isSharedCheck_2211_ == 0 {
                            v_unused_2212_ = crate::leanh::lean_ctor_get(v_l_1775_, 4);
                            crate::leanh::lean_dec(v_unused_2212_);
                            v_unused_2213_ = crate::leanh::lean_ctor_get(v_l_1775_, 3);
                            crate::leanh::lean_dec(v_unused_2213_);
                            v_unused_2214_ = crate::leanh::lean_ctor_get(v_l_1775_, 2);
                            crate::leanh::lean_dec(v_unused_2214_);
                            v_unused_2215_ = crate::leanh::lean_ctor_get(v_l_1775_, 1);
                            crate::leanh::lean_dec(v_unused_2215_);
                            v_unused_2216_ = crate::leanh::lean_ctor_get(v_l_1775_, 0);
                            crate::leanh::lean_dec(v_unused_2216_);
                            v___x_2189_ = v_l_1775_;
                            v_isShared_2190_ = v_isSharedCheck_2211_;
                            state = 61;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_1775_);
                            v___x_2189_ = crate::leanh::lean_box(0);
                            v_isShared_2190_ = v_isSharedCheck_2211_;
                            state = 61;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_r_1952_) == 0 {
                            crate::leanh::lean_inc(v_l_1951_);
                            crate::leanh::lean_inc(v_v_1950_);
                            crate::leanh::lean_inc(v_k_1949_);
                            v_isSharedCheck_2241_ =
                                (!crate::leanh::lean_is_exclusive(v_l_1775_)) as u8;
                            if v_isSharedCheck_2241_ == 0 {
                                v_unused_2242_ = crate::leanh::lean_ctor_get(v_l_1775_, 4);
                                crate::leanh::lean_dec(v_unused_2242_);
                                v_unused_2243_ = crate::leanh::lean_ctor_get(v_l_1775_, 3);
                                crate::leanh::lean_dec(v_unused_2243_);
                                v_unused_2244_ = crate::leanh::lean_ctor_get(v_l_1775_, 2);
                                crate::leanh::lean_dec(v_unused_2244_);
                                v_unused_2245_ = crate::leanh::lean_ctor_get(v_l_1775_, 1);
                                crate::leanh::lean_dec(v_unused_2245_);
                                v_unused_2246_ = crate::leanh::lean_ctor_get(v_l_1775_, 0);
                                crate::leanh::lean_dec(v_unused_2246_);
                                v___x_2218_ = v_l_1775_;
                                v_isShared_2219_ = v_isSharedCheck_2241_;
                                state = 66;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_l_1775_);
                                v___x_2218_ = crate::leanh::lean_box(0);
                                v_isShared_2219_ = v_isSharedCheck_2241_;
                                state = 66;
                                continue;
                            }
                        } else {
                            v_k_2247_ = crate::leanh::lean_ctor_get(v___x_2104_, 0);
                            crate::leanh::lean_inc(v_k_2247_);
                            v_v_2248_ = crate::leanh::lean_ctor_get(v___x_2104_, 1);
                            crate::leanh::lean_inc(v_v_2248_);
                            crate::leanh::lean_dec_ref(v___x_2104_);
                            v___x_2249_ = crate::leanh::lean_unsigned_to_nat(2);
                            if v_isShared_2103_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2102_, 4, v_r_1952_);
                                crate::leanh::lean_ctor_set(v___x_2102_, 3, v_l_1775_);
                                crate::leanh::lean_ctor_set(v___x_2102_, 2, v_v_2248_);
                                crate::leanh::lean_ctor_set(v___x_2102_, 1, v_k_2247_);
                                crate::leanh::lean_ctor_set(v___x_2102_, 0, v___x_2249_);
                                v___x_2251_ = v___x_2102_;
                                state = 71;
                                continue;
                            } else {
                                v_reuseFailAlloc_2252_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_k_2247_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 2, v_v_2248_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 3, v_l_1775_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 4, v_r_1952_);
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
                v_size_2120_ = crate::leanh::lean_ctor_get(v_l_1951_, 0);
                v_size_2121_ = crate::leanh::lean_ctor_get(v_r_1952_, 0);
                v_k_2122_ = crate::leanh::lean_ctor_get(v_r_1952_, 1);
                v_v_2123_ = crate::leanh::lean_ctor_get(v_r_1952_, 2);
                v_l_2124_ = crate::leanh::lean_ctor_get(v_r_1952_, 3);
                v_r_2125_ = crate::leanh::lean_ctor_get(v_r_1952_, 4);
                v___x_2126_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2127_ = lean_nat_mul(v___x_2126_, v_size_2120_);
                v___x_2128_ = lean_nat_dec_lt(v_size_2121_, v___x_2127_);
                crate::leanh::lean_dec(v___x_2127_);
                if v___x_2128_ == 0 {
                    crate::leanh::lean_inc(v_r_2125_);
                    crate::leanh::lean_inc(v_l_2124_);
                    crate::leanh::lean_inc(v_v_2123_);
                    crate::leanh::lean_inc(v_k_2122_);
                    crate::leanh::lean_del_object(v___x_2118_);
                    v_isSharedCheck_2166_ = (!crate::leanh::lean_is_exclusive(v_r_1952_)) as u8;
                    if v_isSharedCheck_2166_ == 0 {
                        v_unused_2167_ = crate::leanh::lean_ctor_get(v_r_1952_, 4);
                        crate::leanh::lean_dec(v_unused_2167_);
                        v_unused_2168_ = crate::leanh::lean_ctor_get(v_r_1952_, 3);
                        crate::leanh::lean_dec(v_unused_2168_);
                        v_unused_2169_ = crate::leanh::lean_ctor_get(v_r_1952_, 2);
                        crate::leanh::lean_dec(v_unused_2169_);
                        v_unused_2170_ = crate::leanh::lean_ctor_get(v_r_1952_, 1);
                        crate::leanh::lean_dec(v_unused_2170_);
                        v_unused_2171_ = crate::leanh::lean_ctor_get(v_r_1952_, 0);
                        crate::leanh::lean_dec(v_unused_2171_);
                        v___x_2130_ = v_r_1952_;
                        v_isShared_2131_ = v_isSharedCheck_2166_;
                        state = 52;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_1952_);
                        v___x_2130_ = crate::leanh::lean_box(0);
                        v_isShared_2131_ = v_isSharedCheck_2166_;
                        state = 52;
                        continue;
                    }
                } else {
                    v___x_2172_ = lean_nat_add(v___x_1958_, v_size_1948_);
                    crate::leanh::lean_dec(v_size_1948_);
                    v___x_2173_ = lean_nat_add(v___x_2172_, v_size_2108_);
                    crate::leanh::lean_dec(v___x_2172_);
                    v___x_2174_ = lean_nat_add(v___x_1958_, v_size_2108_);
                    v___x_2175_ = lean_nat_add(v___x_2174_, v_size_2121_);
                    crate::leanh::lean_dec(v___x_2174_);
                    if v_isShared_2103_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2102_, 4, v_tree_2105_);
                        crate::leanh::lean_ctor_set(v___x_2102_, 3, v_r_1952_);
                        crate::leanh::lean_ctor_set(v___x_2102_, 2, v_v_2107_);
                        crate::leanh::lean_ctor_set(v___x_2102_, 1, v_k_2106_);
                        crate::leanh::lean_ctor_set(v___x_2102_, 0, v___x_2175_);
                        v___x_2177_ = v___x_2102_;
                        state = 59;
                        continue;
                    } else {
                        v_reuseFailAlloc_2181_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2175_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_k_2106_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_v_2107_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 3, v_r_1952_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 4, v_tree_2105_);
                        v___x_2177_ = v_reuseFailAlloc_2181_;
                        state = 59;
                        continue;
                    }
                }
            }
            52 => {
                v___x_2132_ = lean_nat_add(v___x_1958_, v_size_1948_);
                crate::leanh::lean_dec(v_size_1948_);
                v___x_2133_ = lean_nat_add(v___x_2132_, v_size_2108_);
                crate::leanh::lean_dec(v___x_2132_);
                v___x_2154_ = lean_nat_add(v___x_1958_, v_size_2120_);
                if crate::leanh::lean_obj_tag(v_l_2124_) == 0 {
                    v_size_2164_ = crate::leanh::lean_ctor_get(v_l_2124_, 0);
                    crate::leanh::lean_inc(v_size_2164_);
                    v___y_2156_ = v_size_2164_;
                    state = 57;
                    continue;
                } else {
                    v___x_2165_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2156_ = v___x_2165_;
                    state = 57;
                    continue;
                }
            }
            53 => {
                v___x_2138_ = lean_nat_add(v___y_2136_, v___y_2137_);
                crate::leanh::lean_dec(v___y_2137_);
                crate::leanh::lean_dec(v___y_2136_);
                crate::leanh::lean_inc_ref(v_tree_2105_);
                if v_isShared_2131_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2130_, 4, v_tree_2105_);
                    crate::leanh::lean_ctor_set(v___x_2130_, 3, v_r_2125_);
                    crate::leanh::lean_ctor_set(v___x_2130_, 2, v_v_2107_);
                    crate::leanh::lean_ctor_set(v___x_2130_, 1, v_k_2106_);
                    crate::leanh::lean_ctor_set(v___x_2130_, 0, v___x_2138_);
                    v___x_2140_ = v___x_2130_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_2153_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_k_2106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_v_2107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2153_, 3, v_r_2125_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2153_, 4, v_tree_2105_);
                    v___x_2140_ = v_reuseFailAlloc_2153_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                v_isSharedCheck_2147_ = (!crate::leanh::lean_is_exclusive(v_tree_2105_)) as u8;
                if v_isSharedCheck_2147_ == 0 {
                    v_unused_2148_ = crate::leanh::lean_ctor_get(v_tree_2105_, 4);
                    crate::leanh::lean_dec(v_unused_2148_);
                    v_unused_2149_ = crate::leanh::lean_ctor_get(v_tree_2105_, 3);
                    crate::leanh::lean_dec(v_unused_2149_);
                    v_unused_2150_ = crate::leanh::lean_ctor_get(v_tree_2105_, 2);
                    crate::leanh::lean_dec(v_unused_2150_);
                    v_unused_2151_ = crate::leanh::lean_ctor_get(v_tree_2105_, 1);
                    crate::leanh::lean_dec(v_unused_2151_);
                    v_unused_2152_ = crate::leanh::lean_ctor_get(v_tree_2105_, 0);
                    crate::leanh::lean_dec(v_unused_2152_);
                    v___x_2142_ = v_tree_2105_;
                    v_isShared_2143_ = v_isSharedCheck_2147_;
                    state = 55;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tree_2105_);
                    v___x_2142_ = crate::leanh::lean_box(0);
                    v_isShared_2143_ = v_isSharedCheck_2147_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                if v_isShared_2143_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2142_, 4, v___x_2140_);
                    crate::leanh::lean_ctor_set(v___x_2142_, 3, v___y_2135_);
                    crate::leanh::lean_ctor_set(v___x_2142_, 2, v_v_2123_);
                    crate::leanh::lean_ctor_set(v___x_2142_, 1, v_k_2122_);
                    crate::leanh::lean_ctor_set(v___x_2142_, 0, v___x_2133_);
                    v___x_2145_ = v___x_2142_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_2146_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2133_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_k_2122_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 2, v_v_2123_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 3, v___y_2135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 4, v___x_2140_);
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
                crate::leanh::lean_dec(v___y_2156_);
                crate::leanh::lean_dec(v___x_2154_);
                if v_isShared_2103_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2102_, 4, v_l_2124_);
                    crate::leanh::lean_ctor_set(v___x_2102_, 3, v_l_1951_);
                    crate::leanh::lean_ctor_set(v___x_2102_, 2, v_v_1950_);
                    crate::leanh::lean_ctor_set(v___x_2102_, 1, v_k_1949_);
                    crate::leanh::lean_ctor_set(v___x_2102_, 0, v___x_2157_);
                    v___x_2159_ = v___x_2102_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_2163_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_k_1949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_v_1950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 3, v_l_1951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 4, v_l_2124_);
                    v___x_2159_ = v_reuseFailAlloc_2163_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                v___x_2160_ = lean_nat_add(v___x_1958_, v_size_2108_);
                if crate::leanh::lean_obj_tag(v_r_2125_) == 0 {
                    v_size_2161_ = crate::leanh::lean_ctor_get(v_r_2125_, 0);
                    crate::leanh::lean_inc(v_size_2161_);
                    v___y_2135_ = v___x_2159_;
                    v___y_2136_ = v___x_2160_;
                    v___y_2137_ = v_size_2161_;
                    state = 53;
                    continue;
                } else {
                    v___x_2162_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2135_ = v___x_2159_;
                    v___y_2136_ = v___x_2160_;
                    v___y_2137_ = v___x_2162_;
                    state = 53;
                    continue;
                }
            }
            59 => {
                if v_isShared_2119_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2118_, 4, v___x_2177_);
                    crate::leanh::lean_ctor_set(v___x_2118_, 0, v___x_2173_);
                    v___x_2179_ = v___x_2118_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2180_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_k_1949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_v_1950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2180_, 3, v_l_1951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2180_, 4, v___x_2177_);
                    v___x_2179_ = v_reuseFailAlloc_2180_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_2179_;
            }
            61 => {
                if crate::leanh::lean_obj_tag(v_r_1952_) == 0 {
                    v_k_2191_ = crate::leanh::lean_ctor_get(v___x_2104_, 0);
                    crate::leanh::lean_inc(v_k_2191_);
                    v_v_2192_ = crate::leanh::lean_ctor_get(v___x_2104_, 1);
                    crate::leanh::lean_inc(v_v_2192_);
                    crate::leanh::lean_dec_ref(v___x_2104_);
                    v_size_2193_ = crate::leanh::lean_ctor_get(v_r_1952_, 0);
                    v___x_2194_ = lean_nat_add(v___x_1958_, v_size_1948_);
                    crate::leanh::lean_dec(v_size_1948_);
                    v___x_2195_ = lean_nat_add(v___x_1958_, v_size_2193_);
                    if v_isShared_2103_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2102_, 4, v_tree_2105_);
                        crate::leanh::lean_ctor_set(v___x_2102_, 3, v_r_1952_);
                        crate::leanh::lean_ctor_set(v___x_2102_, 2, v_v_2192_);
                        crate::leanh::lean_ctor_set(v___x_2102_, 1, v_k_2191_);
                        crate::leanh::lean_ctor_set(v___x_2102_, 0, v___x_2195_);
                        v___x_2197_ = v___x_2102_;
                        state = 62;
                        continue;
                    } else {
                        v_reuseFailAlloc_2201_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2195_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_k_2191_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_v_2192_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_r_1952_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 4, v_tree_2105_);
                        v___x_2197_ = v_reuseFailAlloc_2201_;
                        state = 62;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_size_1948_);
                    v_k_2202_ = crate::leanh::lean_ctor_get(v___x_2104_, 0);
                    crate::leanh::lean_inc(v_k_2202_);
                    v_v_2203_ = crate::leanh::lean_ctor_get(v___x_2104_, 1);
                    crate::leanh::lean_inc(v_v_2203_);
                    crate::leanh::lean_dec_ref(v___x_2104_);
                    v___x_2204_ = crate::leanh::lean_unsigned_to_nat(3);
                    if v_isShared_2103_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2102_, 4, v_r_1952_);
                        crate::leanh::lean_ctor_set(v___x_2102_, 3, v_r_1952_);
                        crate::leanh::lean_ctor_set(v___x_2102_, 2, v_v_2203_);
                        crate::leanh::lean_ctor_set(v___x_2102_, 1, v_k_2202_);
                        crate::leanh::lean_ctor_set(v___x_2102_, 0, v___x_1958_);
                        v___x_2206_ = v___x_2102_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_2210_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_1958_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_k_2202_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_v_2203_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 3, v_r_1952_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 4, v_r_1952_);
                        v___x_2206_ = v_reuseFailAlloc_2210_;
                        state = 64;
                        continue;
                    }
                }
            }
            62 => {
                if v_isShared_2190_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2189_, 4, v___x_2197_);
                    crate::leanh::lean_ctor_set(v___x_2189_, 0, v___x_2194_);
                    v___x_2199_ = v___x_2189_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_2200_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_k_1949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_v_1950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 3, v_l_1951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 4, v___x_2197_);
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
                    crate::leanh::lean_ctor_set(v___x_2189_, 4, v___x_2206_);
                    crate::leanh::lean_ctor_set(v___x_2189_, 0, v___x_2204_);
                    v___x_2208_ = v___x_2189_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2209_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2204_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_k_1949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_v_1950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 3, v_l_1951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 4, v___x_2206_);
                    v___x_2208_ = v_reuseFailAlloc_2209_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_2208_;
            }
            66 => {
                v_k_2220_ = crate::leanh::lean_ctor_get(v___x_2104_, 0);
                crate::leanh::lean_inc(v_k_2220_);
                v_v_2221_ = crate::leanh::lean_ctor_get(v___x_2104_, 1);
                crate::leanh::lean_inc(v_v_2221_);
                crate::leanh::lean_dec_ref(v___x_2104_);
                v_k_2222_ = crate::leanh::lean_ctor_get(v_r_1952_, 1);
                v_v_2223_ = crate::leanh::lean_ctor_get(v_r_1952_, 2);
                v_isSharedCheck_2237_ = (!crate::leanh::lean_is_exclusive(v_r_1952_)) as u8;
                if v_isSharedCheck_2237_ == 0 {
                    v_unused_2238_ = crate::leanh::lean_ctor_get(v_r_1952_, 4);
                    crate::leanh::lean_dec(v_unused_2238_);
                    v_unused_2239_ = crate::leanh::lean_ctor_get(v_r_1952_, 3);
                    crate::leanh::lean_dec(v_unused_2239_);
                    v_unused_2240_ = crate::leanh::lean_ctor_get(v_r_1952_, 0);
                    crate::leanh::lean_dec(v_unused_2240_);
                    v___x_2225_ = v_r_1952_;
                    v_isShared_2226_ = v_isSharedCheck_2237_;
                    state = 67;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2223_);
                    crate::leanh::lean_inc(v_k_2222_);
                    crate::leanh::lean_dec(v_r_1952_);
                    v___x_2225_ = crate::leanh::lean_box(0);
                    v_isShared_2226_ = v_isSharedCheck_2237_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                v___x_2227_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2226_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2225_, 4, v_l_1951_);
                    crate::leanh::lean_ctor_set(v___x_2225_, 3, v_l_1951_);
                    crate::leanh::lean_ctor_set(v___x_2225_, 2, v_v_1950_);
                    crate::leanh::lean_ctor_set(v___x_2225_, 1, v_k_1949_);
                    crate::leanh::lean_ctor_set(v___x_2225_, 0, v___x_1958_);
                    v___x_2229_ = v___x_2225_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_2236_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_1958_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_k_1949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 2, v_v_1950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 3, v_l_1951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 4, v_l_1951_);
                    v___x_2229_ = v_reuseFailAlloc_2236_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                if v_isShared_2103_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2102_, 4, v_l_1951_);
                    crate::leanh::lean_ctor_set(v___x_2102_, 3, v_l_1951_);
                    crate::leanh::lean_ctor_set(v___x_2102_, 2, v_v_2221_);
                    crate::leanh::lean_ctor_set(v___x_2102_, 1, v_k_2220_);
                    crate::leanh::lean_ctor_set(v___x_2102_, 0, v___x_1958_);
                    v___x_2231_ = v___x_2102_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_2235_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_1958_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_k_2220_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_v_2221_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_l_1951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 4, v_l_1951_);
                    v___x_2231_ = v_reuseFailAlloc_2235_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                if v_isShared_2219_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2218_, 4, v___x_2231_);
                    crate::leanh::lean_ctor_set(v___x_2218_, 3, v___x_2229_);
                    crate::leanh::lean_ctor_set(v___x_2218_, 2, v_v_2223_);
                    crate::leanh::lean_ctor_set(v___x_2218_, 1, v_k_2222_);
                    crate::leanh::lean_ctor_set(v___x_2218_, 0, v___x_2227_);
                    v___x_2233_ = v___x_2218_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_2234_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_k_2222_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 2, v_v_2223_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 3, v___x_2229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 4, v___x_2231_);
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
                v_size_2278_ = crate::leanh::lean_ctor_get(v_l_2265_, 0);
                v_k_2279_ = crate::leanh::lean_ctor_get(v_l_2265_, 1);
                v_v_2280_ = crate::leanh::lean_ctor_get(v_l_2265_, 2);
                v_l_2281_ = crate::leanh::lean_ctor_get(v_l_2265_, 3);
                v_r_2282_ = crate::leanh::lean_ctor_get(v_l_2265_, 4);
                v_size_2283_ = crate::leanh::lean_ctor_get(v_r_2266_, 0);
                v___x_2284_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2285_ = lean_nat_mul(v___x_2284_, v_size_2283_);
                v___x_2286_ = lean_nat_dec_lt(v_size_2278_, v___x_2285_);
                crate::leanh::lean_dec(v___x_2285_);
                if v___x_2286_ == 0 {
                    crate::leanh::lean_inc(v_r_2282_);
                    crate::leanh::lean_inc(v_l_2281_);
                    crate::leanh::lean_inc(v_v_2280_);
                    crate::leanh::lean_inc(v_k_2279_);
                    v_isSharedCheck_2314_ = (!crate::leanh::lean_is_exclusive(v_l_2265_)) as u8;
                    if v_isSharedCheck_2314_ == 0 {
                        v_unused_2315_ = crate::leanh::lean_ctor_get(v_l_2265_, 4);
                        crate::leanh::lean_dec(v_unused_2315_);
                        v_unused_2316_ = crate::leanh::lean_ctor_get(v_l_2265_, 3);
                        crate::leanh::lean_dec(v_unused_2316_);
                        v_unused_2317_ = crate::leanh::lean_ctor_get(v_l_2265_, 2);
                        crate::leanh::lean_dec(v_unused_2317_);
                        v_unused_2318_ = crate::leanh::lean_ctor_get(v_l_2265_, 1);
                        crate::leanh::lean_dec(v_unused_2318_);
                        v_unused_2319_ = crate::leanh::lean_ctor_get(v_l_2265_, 0);
                        crate::leanh::lean_dec(v_unused_2319_);
                        v___x_2288_ = v_l_2265_;
                        v_isShared_2289_ = v_isSharedCheck_2314_;
                        state = 74;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_2265_);
                        v___x_2288_ = crate::leanh::lean_box(0);
                        v_isShared_2289_ = v_isSharedCheck_2314_;
                        state = 74;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1778_);
                    v___x_2320_ = lean_nat_add(v___x_2260_, v_size_2261_);
                    crate::leanh::lean_dec(v_size_2261_);
                    v___x_2321_ = lean_nat_add(v___x_2320_, v_size_2262_);
                    crate::leanh::lean_dec(v_size_2262_);
                    v___x_2322_ = lean_nat_add(v___x_2320_, v_size_2278_);
                    crate::leanh::lean_dec(v___x_2320_);
                    crate::leanh::lean_inc_ref(v_impl_2259_);
                    if v_isShared_2277_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2276_, 4, v_l_2265_);
                        crate::leanh::lean_ctor_set(v___x_2276_, 3, v_impl_2259_);
                        crate::leanh::lean_ctor_set(v___x_2276_, 2, v_v_1774_);
                        crate::leanh::lean_ctor_set(v___x_2276_, 1, v_k_1773_);
                        crate::leanh::lean_ctor_set(v___x_2276_, 0, v___x_2322_);
                        v___x_2324_ = v___x_2276_;
                        state = 80;
                        continue;
                    } else {
                        v_reuseFailAlloc_2337_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2322_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_k_1773_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 2, v_v_1774_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 3, v_impl_2259_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 4, v_l_2265_);
                        v___x_2324_ = v_reuseFailAlloc_2337_;
                        state = 80;
                        continue;
                    }
                }
            }
            74 => {
                v___x_2290_ = lean_nat_add(v___x_2260_, v_size_2261_);
                crate::leanh::lean_dec(v_size_2261_);
                v___x_2291_ = lean_nat_add(v___x_2290_, v_size_2262_);
                crate::leanh::lean_dec(v_size_2262_);
                if crate::leanh::lean_obj_tag(v_l_2281_) == 0 {
                    v_size_2312_ = crate::leanh::lean_ctor_get(v_l_2281_, 0);
                    crate::leanh::lean_inc(v_size_2312_);
                    v___y_2304_ = v_size_2312_;
                    state = 78;
                    continue;
                } else {
                    v___x_2313_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2304_ = v___x_2313_;
                    state = 78;
                    continue;
                }
            }
            75 => {
                v___x_2296_ = lean_nat_add(v___y_2293_, v___y_2295_);
                crate::leanh::lean_dec(v___y_2295_);
                crate::leanh::lean_dec(v___y_2293_);
                if v_isShared_2289_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2288_, 4, v_r_2266_);
                    crate::leanh::lean_ctor_set(v___x_2288_, 3, v_r_2282_);
                    crate::leanh::lean_ctor_set(v___x_2288_, 2, v_v_2264_);
                    crate::leanh::lean_ctor_set(v___x_2288_, 1, v_k_2263_);
                    crate::leanh::lean_ctor_set(v___x_2288_, 0, v___x_2296_);
                    v___x_2298_ = v___x_2288_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_2302_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2296_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2302_, 1, v_k_2263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2302_, 2, v_v_2264_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2302_, 3, v_r_2282_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2302_, 4, v_r_2266_);
                    v___x_2298_ = v_reuseFailAlloc_2302_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                if v_isShared_2277_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2276_, 4, v___x_2298_);
                    crate::leanh::lean_ctor_set(v___x_2276_, 3, v___y_2294_);
                    crate::leanh::lean_ctor_set(v___x_2276_, 2, v_v_2280_);
                    crate::leanh::lean_ctor_set(v___x_2276_, 1, v_k_2279_);
                    crate::leanh::lean_ctor_set(v___x_2276_, 0, v___x_2291_);
                    v___x_2300_ = v___x_2276_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_2301_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2291_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_k_2279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 2, v_v_2280_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 3, v___y_2294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 4, v___x_2298_);
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
                crate::leanh::lean_dec(v___y_2304_);
                crate::leanh::lean_dec(v___x_2290_);
                if v_isShared_1779_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1778_, 4, v_l_2281_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 3, v_impl_2259_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_2305_);
                    v___x_2307_ = v___x_1778_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_2311_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2305_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_k_1773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 2, v_v_1774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 3, v_impl_2259_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 4, v_l_2281_);
                    v___x_2307_ = v_reuseFailAlloc_2311_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                v___x_2308_ = lean_nat_add(v___x_2260_, v_size_2283_);
                if crate::leanh::lean_obj_tag(v_r_2282_) == 0 {
                    v_size_2309_ = crate::leanh::lean_ctor_get(v_r_2282_, 0);
                    crate::leanh::lean_inc(v_size_2309_);
                    v___y_2293_ = v___x_2308_;
                    v___y_2294_ = v___x_2307_;
                    v___y_2295_ = v_size_2309_;
                    state = 75;
                    continue;
                } else {
                    v___x_2310_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2293_ = v___x_2308_;
                    v___y_2294_ = v___x_2307_;
                    v___y_2295_ = v___x_2310_;
                    state = 75;
                    continue;
                }
            }
            80 => {
                v_isSharedCheck_2331_ = (!crate::leanh::lean_is_exclusive(v_impl_2259_)) as u8;
                if v_isSharedCheck_2331_ == 0 {
                    v_unused_2332_ = crate::leanh::lean_ctor_get(v_impl_2259_, 4);
                    crate::leanh::lean_dec(v_unused_2332_);
                    v_unused_2333_ = crate::leanh::lean_ctor_get(v_impl_2259_, 3);
                    crate::leanh::lean_dec(v_unused_2333_);
                    v_unused_2334_ = crate::leanh::lean_ctor_get(v_impl_2259_, 2);
                    crate::leanh::lean_dec(v_unused_2334_);
                    v_unused_2335_ = crate::leanh::lean_ctor_get(v_impl_2259_, 1);
                    crate::leanh::lean_dec(v_unused_2335_);
                    v_unused_2336_ = crate::leanh::lean_ctor_get(v_impl_2259_, 0);
                    crate::leanh::lean_dec(v_unused_2336_);
                    v___x_2326_ = v_impl_2259_;
                    v_isShared_2327_ = v_isSharedCheck_2331_;
                    state = 81;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_impl_2259_);
                    v___x_2326_ = crate::leanh::lean_box(0);
                    v_isShared_2327_ = v_isSharedCheck_2331_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                if v_isShared_2327_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2326_, 4, v_r_2266_);
                    crate::leanh::lean_ctor_set(v___x_2326_, 3, v___x_2324_);
                    crate::leanh::lean_ctor_set(v___x_2326_, 2, v_v_2264_);
                    crate::leanh::lean_ctor_set(v___x_2326_, 1, v_k_2263_);
                    crate::leanh::lean_ctor_set(v___x_2326_, 0, v___x_2321_);
                    v___x_2329_ = v___x_2326_;
                    state = 82;
                    continue;
                } else {
                    v_reuseFailAlloc_2330_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_k_2263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 2, v_v_2264_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 3, v___x_2324_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 4, v_r_2266_);
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
                v_size_2357_ = crate::leanh::lean_ctor_get(v_l_2349_, 0);
                v___x_2358_ = lean_nat_add(v___x_2260_, v_size_2351_);
                crate::leanh::lean_dec(v_size_2351_);
                v___x_2359_ = lean_nat_add(v___x_2260_, v_size_2357_);
                if v_isShared_2356_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2355_, 4, v_l_2349_);
                    crate::leanh::lean_ctor_set(v___x_2355_, 3, v_impl_2259_);
                    crate::leanh::lean_ctor_set(v___x_2355_, 2, v_v_1774_);
                    crate::leanh::lean_ctor_set(v___x_2355_, 1, v_k_1773_);
                    crate::leanh::lean_ctor_set(v___x_2355_, 0, v___x_2359_);
                    v___x_2361_ = v___x_2355_;
                    state = 85;
                    continue;
                } else {
                    v_reuseFailAlloc_2365_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_k_1773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 2, v_v_1774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 3, v_impl_2259_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 4, v_l_2349_);
                    v___x_2361_ = v_reuseFailAlloc_2365_;
                    state = 85;
                    continue;
                }
            }
            85 => {
                if v_isShared_1779_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1778_, 4, v_r_2350_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 3, v___x_2361_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 2, v_v_2353_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 1, v_k_2352_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_2358_);
                    v___x_2363_ = v___x_1778_;
                    state = 86;
                    continue;
                } else {
                    v_reuseFailAlloc_2364_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2358_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_k_2352_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 2, v_v_2353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 3, v___x_2361_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 4, v_r_2350_);
                    v___x_2363_ = v_reuseFailAlloc_2364_;
                    state = 86;
                    continue;
                }
            }
            86 => {
                return v___x_2363_;
            }
            87 => {
                v_k_2374_ = crate::leanh::lean_ctor_get(v_l_2349_, 1);
                v_v_2375_ = crate::leanh::lean_ctor_get(v_l_2349_, 2);
                v_isSharedCheck_2389_ = (!crate::leanh::lean_is_exclusive(v_l_2349_)) as u8;
                if v_isSharedCheck_2389_ == 0 {
                    v_unused_2390_ = crate::leanh::lean_ctor_get(v_l_2349_, 4);
                    crate::leanh::lean_dec(v_unused_2390_);
                    v_unused_2391_ = crate::leanh::lean_ctor_get(v_l_2349_, 3);
                    crate::leanh::lean_dec(v_unused_2391_);
                    v_unused_2392_ = crate::leanh::lean_ctor_get(v_l_2349_, 0);
                    crate::leanh::lean_dec(v_unused_2392_);
                    v___x_2377_ = v_l_2349_;
                    v_isShared_2378_ = v_isSharedCheck_2389_;
                    state = 88;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2375_);
                    crate::leanh::lean_inc(v_k_2374_);
                    crate::leanh::lean_dec(v_l_2349_);
                    v___x_2377_ = crate::leanh::lean_box(0);
                    v_isShared_2378_ = v_isSharedCheck_2389_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                v___x_2379_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2378_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2377_, 4, v_r_2350_);
                    crate::leanh::lean_ctor_set(v___x_2377_, 3, v_r_2350_);
                    crate::leanh::lean_ctor_set(v___x_2377_, 2, v_v_1774_);
                    crate::leanh::lean_ctor_set(v___x_2377_, 1, v_k_1773_);
                    crate::leanh::lean_ctor_set(v___x_2377_, 0, v___x_2260_);
                    v___x_2381_ = v___x_2377_;
                    state = 89;
                    continue;
                } else {
                    v_reuseFailAlloc_2388_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2260_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_k_1773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 2, v_v_1774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 3, v_r_2350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 4, v_r_2350_);
                    v___x_2381_ = v_reuseFailAlloc_2388_;
                    state = 89;
                    continue;
                }
            }
            89 => {
                if v_isShared_2373_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2372_, 3, v_r_2350_);
                    crate::leanh::lean_ctor_set(v___x_2372_, 0, v___x_2260_);
                    v___x_2383_ = v___x_2372_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_2387_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2260_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 1, v_k_2369_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 2, v_v_2370_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 3, v_r_2350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 4, v_r_2350_);
                    v___x_2383_ = v_reuseFailAlloc_2387_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_1779_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1778_, 4, v___x_2383_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 3, v___x_2381_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 2, v_v_2375_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 1, v_k_2374_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_2379_);
                    v___x_2385_ = v___x_1778_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_k_2374_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 2, v_v_2375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 3, v___x_2381_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 4, v___x_2383_);
                    v___x_2385_ = v_reuseFailAlloc_2386_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_2385_;
            }
            92 => {
                v___x_2403_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2402_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2401_, 4, v_l_2349_);
                    crate::leanh::lean_ctor_set(v___x_2401_, 2, v_v_1774_);
                    crate::leanh::lean_ctor_set(v___x_2401_, 1, v_k_1773_);
                    crate::leanh::lean_ctor_set(v___x_2401_, 0, v___x_2260_);
                    v___x_2405_ = v___x_2401_;
                    state = 93;
                    continue;
                } else {
                    v_reuseFailAlloc_2409_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2260_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 1, v_k_1773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 2, v_v_1774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 3, v_l_2349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 4, v_l_2349_);
                    v___x_2405_ = v_reuseFailAlloc_2409_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                if v_isShared_1779_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1778_, 4, v_r_2397_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 3, v___x_2405_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 2, v_v_2399_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 1, v_k_2398_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_2403_);
                    v___x_2407_ = v___x_1778_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_2408_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2403_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2408_, 1, v_k_2398_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2408_, 2, v_v_2399_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2408_, 3, v___x_2405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2408_, 4, v_r_2397_);
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
                    crate::leanh::lean_ctor_set(v___x_2418_, 3, v_r_2397_);
                    v___x_2421_ = v___x_2418_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_size_2414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_k_2415_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 2, v_v_2416_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 3, v_r_2397_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 4, v_r_2397_);
                    v___x_2421_ = v_reuseFailAlloc_2426_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                v___x_2422_ = crate::leanh::lean_unsigned_to_nat(2);
                if v_isShared_1779_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1778_, 4, v___x_2421_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 3, v_r_2397_);
                    crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_2422_);
                    v___x_2424_ = v___x_1778_;
                    state = 97;
                    continue;
                } else {
                    v_reuseFailAlloc_2425_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_k_1773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2425_, 2, v_v_1774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2425_, 3, v_r_2397_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2425_, 4, v___x_2421_);
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
    mut v_k_2435_: *mut crate::leanh::LeanObject,
    mut v_t_2436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_boxed_2437_: u64 = 0;
    let mut v_res_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_2437_ = crate::leanh::lean_unbox_uint64(v_k_2435_);
    crate::leanh::lean_dec_ref(v_k_2435_);
    v_res_2438_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_boxed_2437_, v_t_2436_);
    return v_res_2438_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(
    mut v_t_2439_: *mut crate::leanh::LeanObject,
    mut v_k_2440_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u64 = 0;
    let mut v___x_2446_: u8 = 0;
    let mut v___x_2447_: u64 = 0;
    let mut v___x_2448_: u8 = 0;
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2439_) == 0 {
                    v_k_2441_ = crate::leanh::lean_ctor_get(v_t_2439_, 1);
                    v_v_2442_ = crate::leanh::lean_ctor_get(v_t_2439_, 2);
                    v_l_2443_ = crate::leanh::lean_ctor_get(v_t_2439_, 3);
                    v_r_2444_ = crate::leanh::lean_ctor_get(v_t_2439_, 4);
                    v___x_2445_ = crate::leanh::lean_unbox_uint64(v_k_2441_);
                    v___x_2446_ = lean_uint64_dec_lt(v_k_2440_, v___x_2445_);
                    if v___x_2446_ == 0 {
                        v___x_2447_ = crate::leanh::lean_unbox_uint64(v_k_2441_);
                        v___x_2448_ = lean_uint64_dec_eq(v_k_2440_, v___x_2447_);
                        if v___x_2448_ == 0 {
                            v_t_2439_ = v_r_2444_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_v_2442_);
                            v___x_2450_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2450_, 0, v_v_2442_);
                            return v___x_2450_;
                        }
                    } else {
                        v_t_2439_ = v_l_2443_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_2452_ = crate::leanh::lean_box(0);
                    return v___x_2452_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg___boxed(
    mut v_t_2453_: *mut crate::leanh::LeanObject,
    mut v_k_2454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_boxed_2455_: u64 = 0;
    let mut v_res_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_2455_ = crate::leanh::lean_unbox_uint64(v_k_2454_);
    crate::leanh::lean_dec_ref(v_k_2454_);
    v_res_2456_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_t_2453_, v_k_boxed_2455_);
    crate::leanh::lean_dec(v_t_2453_);
    return v_res_2456_;
}
pub unsafe fn l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(
    mut v_state_2457_: *mut crate::leanh::LeanObject,
    mut v_id_2458_: u64,
    mut v_reason_2459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tokens_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2466_: usize = 0;
    let mut v___x_2467_: usize = 0;
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tokens_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_2471_: u64 = 0;
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2474_: u8 = 0;
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tokens_2461_ = crate::leanh::lean_ctor_get(v_state_2457_, 0);
                v___x_2462_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_tokens_2461_, v_id_2458_);
                if crate::leanh::lean_obj_tag(v___x_2462_) == 1 {
                    v_val_2463_ = crate::leanh::lean_ctor_get(v___x_2462_, 0);
                    crate::leanh::lean_inc(v_val_2463_);
                    crate::leanh::lean_dec_ref_known(v___x_2462_, 1);
                    v_fst_2464_ = crate::leanh::lean_ctor_get(v_val_2463_, 0);
                    crate::leanh::lean_inc(v_fst_2464_);
                    v_snd_2465_ = crate::leanh::lean_ctor_get(v_val_2463_, 1);
                    crate::leanh::lean_inc(v_snd_2465_);
                    crate::leanh::lean_dec(v_val_2463_);
                    v_sz_2466_ = lean_array_size(v_snd_2465_);
                    v___x_2467_ = 0usize;
                    crate::leanh::lean_inc(v_reason_2459_);
                    v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(v_reason_2459_, v_snd_2465_, v_sz_2466_, v___x_2467_, v_state_2457_);
                    crate::leanh::lean_dec(v_snd_2465_);
                    v___x_2469_ = l_Std_CancellationToken_cancel(v_fst_2464_, v_reason_2459_);
                    v_tokens_2470_ = crate::leanh::lean_ctor_get(v___x_2468_, 0);
                    v_id_2471_ = crate::leanh::lean_ctor_get_uint64(
                        v___x_2468_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_isSharedCheck_2479_ = (!crate::leanh::lean_is_exclusive(v___x_2468_)) as u8;
                    if v_isSharedCheck_2479_ == 0 {
                        v___x_2473_ = v___x_2468_;
                        v_isShared_2474_ = v_isSharedCheck_2479_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tokens_2470_);
                        crate::leanh::lean_dec(v___x_2468_);
                        v___x_2473_ = crate::leanh::lean_box(0);
                        v_isShared_2474_ = v_isSharedCheck_2479_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2462_);
                    crate::leanh::lean_dec(v_reason_2459_);
                    return v_state_2457_;
                }
            }
            1 => {
                v___x_2475_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_id_2458_, v_tokens_2470_);
                if v_isShared_2474_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2473_, 0, v___x_2475_);
                    v___x_2477_ = v___x_2473_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2478_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2478_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_reason_2480_: *mut crate::leanh::LeanObject,
    mut v_as_2481_: *mut crate::leanh::LeanObject,
    mut v_sz_2482_: usize,
    mut v_i_2483_: usize,
    mut v_b_2484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2486_: u8 = 0;
    let mut v_a_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: u64 = 0;
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: usize = 0;
    let mut v___x_2491_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2486_ = lean_usize_dec_lt(v_i_2483_, v_sz_2482_);
                if v___x_2486_ == 0 {
                    crate::leanh::lean_dec(v_reason_2480_);
                    return v_b_2484_;
                } else {
                    v_a_2487_ = lean_array_uget_borrowed(v_as_2481_, v_i_2483_);
                    v___x_2488_ = crate::leanh::lean_unbox_uint64(v_a_2487_);
                    crate::leanh::lean_inc(v_reason_2480_);
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
    mut v_reason_2493_: *mut crate::leanh::LeanObject,
    mut v_as_2494_: *mut crate::leanh::LeanObject,
    mut v_sz_2495_: *mut crate::leanh::LeanObject,
    mut v_i_2496_: *mut crate::leanh::LeanObject,
    mut v_b_2497_: *mut crate::leanh::LeanObject,
    mut v___y_2498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2499_: usize = 0;
    let mut v_i_boxed_2500_: usize = 0;
    let mut v_res_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2499_ = crate::leanh::lean_unbox_usize(v_sz_2495_);
    crate::leanh::lean_dec(v_sz_2495_);
    v_i_boxed_2500_ = crate::leanh::lean_unbox_usize(v_i_2496_);
    crate::leanh::lean_dec(v_i_2496_);
    v_res_2501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__1(v_reason_2493_, v_as_2494_, v_sz_boxed_2499_, v_i_boxed_2500_, v_b_2497_);
    crate::leanh::lean_dec_ref(v_as_2494_);
    return v_res_2501_;
}
pub unsafe fn l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren___boxed(
    mut v_state_2502_: *mut crate::leanh::LeanObject,
    mut v_id_2503_: *mut crate::leanh::LeanObject,
    mut v_reason_2504_: *mut crate::leanh::LeanObject,
    mut v_a_2505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_boxed_2506_: u64 = 0;
    let mut v_res_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_id_boxed_2506_ = crate::leanh::lean_unbox_uint64(v_id_2503_);
    crate::leanh::lean_dec_ref(v_id_2503_);
    v_res_2507_ =
        l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren(
            v_state_2502_,
            v_id_boxed_2506_,
            v_reason_2504_,
        );
    return v_res_2507_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(
    mut v_00_u03b4_2508_: *mut crate::leanh::LeanObject,
    mut v_t_2509_: *mut crate::leanh::LeanObject,
    mut v_k_2510_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2511_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_t_2509_, v_k_2510_);
    return v___x_2511_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___boxed(
    mut v_00_u03b4_2512_: *mut crate::leanh::LeanObject,
    mut v_t_2513_: *mut crate::leanh::LeanObject,
    mut v_k_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_boxed_2515_: u64 = 0;
    let mut v_res_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_2515_ = crate::leanh::lean_unbox_uint64(v_k_2514_);
    crate::leanh::lean_dec_ref(v_k_2514_);
    v_res_2516_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0(v_00_u03b4_2512_, v_t_2513_, v_k_boxed_2515_);
    crate::leanh::lean_dec(v_t_2513_);
    return v_res_2516_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(
    mut v_00_u03b2_2517_: *mut crate::leanh::LeanObject,
    mut v_k_2518_: u64,
    mut v_t_2519_: *mut crate::leanh::LeanObject,
    mut v_h_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2521_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___redArg(v_k_2518_, v_t_2519_);
    return v___x_2521_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2___boxed(
    mut v_00_u03b2_2522_: *mut crate::leanh::LeanObject,
    mut v_k_2523_: *mut crate::leanh::LeanObject,
    mut v_t_2524_: *mut crate::leanh::LeanObject,
    mut v_h_2525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_boxed_2526_: u64 = 0;
    let mut v_res_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_2526_ = crate::leanh::lean_unbox_uint64(v_k_2523_);
    crate::leanh::lean_dec_ref(v_k_2523_);
    v_res_2527_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__2(v_00_u03b2_2522_, v_k_boxed_2526_, v_t_2524_, v_h_2525_);
    return v_res_2527_;
}
pub unsafe fn l_Std_CancellationContext_cancel___lam__0(
    mut v_id_2528_: u64,
    mut v_reason_2529_: *mut crate::leanh::LeanObject,
    mut v___y_2530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_id_2535_: *mut crate::leanh::LeanObject,
    mut v_reason_2536_: *mut crate::leanh::LeanObject,
    mut v___y_2537_: *mut crate::leanh::LeanObject,
    mut v___y_2538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_boxed_2539_: u64 = 0;
    let mut v_res_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_id_boxed_2539_ = crate::leanh::lean_unbox_uint64(v_id_2535_);
    crate::leanh::lean_dec_ref(v_id_2535_);
    v_res_2540_ =
        l_Std_CancellationContext_cancel___lam__0(v_id_boxed_2539_, v_reason_2536_, v___y_2537_);
    crate::leanh::lean_dec(v___y_2537_);
    return v_res_2540_;
}
pub unsafe fn l_Std_CancellationContext_cancel(
    mut v_x_2541_: *mut crate::leanh::LeanObject,
    mut v_reason_2542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_state_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_token_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_2546_: u64 = 0;
    let mut v___x_2547_: u8 = 0;
    v_state_2544_ = crate::leanh::lean_ctor_get(v_x_2541_, 0);
    crate::leanh::lean_inc_ref(v_state_2544_);
    v_token_2545_ = crate::leanh::lean_ctor_get(v_x_2541_, 1);
    crate::leanh::lean_inc_ref(v_token_2545_);
    v_id_2546_ = crate::leanh::lean_ctor_get_uint64(
        v_x_2541_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    crate::leanh::lean_dec_ref(v_x_2541_);
    v___x_2547_ = l_Std_CancellationToken_isCancelled(v_token_2545_);
    if v___x_2547_ == 0 {
        let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2548_ = crate::leanh::lean_box_uint64(v_id_2546_);
        v___f_2549_ = crate::leanh::lean_alloc_closure(
            l_Std_CancellationContext_cancel___lam__0___boxed as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2549_, 0, v___x_2548_);
        crate::leanh::lean_closure_set(v___f_2549_, 1, v_reason_2542_);
        v___x_2550_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(
            v_state_2544_,
            v___f_2549_,
        );
        return v___x_2550_;
    } else {
        let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_state_2544_);
        crate::leanh::lean_dec(v_reason_2542_);
        v___x_2551_ = crate::leanh::lean_box(0);
        return v___x_2551_;
    }
}
pub unsafe fn l_Std_CancellationContext_cancel___boxed(
    mut v_x_2552_: *mut crate::leanh::LeanObject,
    mut v_reason_2553_: *mut crate::leanh::LeanObject,
    mut v_a_2554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2555_ = l_Std_CancellationContext_cancel(v_x_2552_, v_reason_2553_);
    return v_res_2555_;
}
pub unsafe fn l_Std_CancellationContext_isCancelled(
    mut v_x_2556_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_token_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: u8 = 0;
    v_token_2558_ = crate::leanh::lean_ctor_get(v_x_2556_, 1);
    crate::leanh::lean_inc_ref(v_token_2558_);
    crate::leanh::lean_dec_ref(v_x_2556_);
    v___x_2559_ = l_Std_CancellationToken_isCancelled(v_token_2558_);
    return v___x_2559_;
}
pub unsafe fn l_Std_CancellationContext_isCancelled___boxed(
    mut v_x_2560_: *mut crate::leanh::LeanObject,
    mut v_a_2561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2562_: u8 = 0;
    let mut v_r_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2562_ = l_Std_CancellationContext_isCancelled(v_x_2560_);
    v_r_2563_ = crate::leanh::lean_box((v_res_2562_) as usize);
    return v_r_2563_;
}
pub unsafe fn l_Std_CancellationContext_getCancellationReason(
    mut v_x_2564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_token_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_token_2566_ = crate::leanh::lean_ctor_get(v_x_2564_, 1);
    crate::leanh::lean_inc_ref(v_token_2566_);
    crate::leanh::lean_dec_ref(v_x_2564_);
    v___x_2567_ = l_Std_CancellationToken_getCancellationReason(v_token_2566_);
    return v___x_2567_;
}
pub unsafe fn l_Std_CancellationContext_getCancellationReason___boxed(
    mut v_x_2568_: *mut crate::leanh::LeanObject,
    mut v_a_2569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2570_ = l_Std_CancellationContext_getCancellationReason(v_x_2568_);
    return v_res_2570_;
}
pub unsafe fn l_Std_CancellationContext_done(
    mut v_x_2571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_token_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_token_2573_ = crate::leanh::lean_ctor_get(v_x_2571_, 1);
    crate::leanh::lean_inc_ref(v_token_2573_);
    crate::leanh::lean_dec_ref(v_x_2571_);
    v___x_2574_ = l_Std_CancellationToken_wait(v_token_2573_);
    return v___x_2574_;
}
pub unsafe fn l_Std_CancellationContext_done___boxed(
    mut v_x_2575_: *mut crate::leanh::LeanObject,
    mut v_a_2576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2577_ = l_Std_CancellationContext_done(v_x_2575_);
    return v_res_2577_;
}
pub unsafe fn l_Std_CancellationContext_doneSelector(
    mut v_x_2578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_token_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_token_2579_ = crate::leanh::lean_ctor_get(v_x_2578_, 1);
    crate::leanh::lean_inc_ref(v_token_2579_);
    crate::leanh::lean_dec_ref(v_x_2578_);
    v___x_2580_ = l_Std_CancellationToken_selector(v_token_2579_);
    return v___x_2580_;
}
pub unsafe fn l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(
    mut v_state_2581_: *mut crate::leanh::LeanObject,
    mut v_id_2582_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v_tokens_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tokens_2583_ = crate::leanh::lean_ctor_get(v_state_2581_, 0);
    v___x_2584_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_cancelChildren_spec__0___redArg(v_tokens_2583_, v_id_2582_);
    if crate::leanh::lean_obj_tag(v___x_2584_) == 0 {
        let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2585_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2585_;
    } else {
        let mut v_val_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2590_: u8 = 0;
        v_val_2586_ = crate::leanh::lean_ctor_get(v___x_2584_, 0);
        crate::leanh::lean_inc(v_val_2586_);
        crate::leanh::lean_dec_ref_known(v___x_2584_, 1);
        v_snd_2587_ = crate::leanh::lean_ctor_get(v_val_2586_, 1);
        crate::leanh::lean_inc(v_snd_2587_);
        crate::leanh::lean_dec(v_val_2586_);
        v___x_2588_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2589_ = lean_array_get_size(v_snd_2587_);
        v___x_2590_ = lean_nat_dec_lt(v___x_2588_, v___x_2589_);
        if v___x_2590_ == 0 {
            let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_snd_2587_);
            v___x_2591_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2591_;
        } else {
            let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2593_: u8 = 0;
            v___x_2592_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_2593_ = lean_nat_dec_le(v___x_2589_, v___x_2589_);
            if v___x_2593_ == 0 {
                if v___x_2590_ == 0 {
                    crate::leanh::lean_dec(v_snd_2587_);
                    return v___x_2592_;
                } else {
                    let mut v___x_2594_: usize = 0;
                    let mut v___x_2595_: usize = 0;
                    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_2594_ = 0usize;
                    v___x_2595_ = lean_usize_of_nat(v___x_2589_);
                    v___x_2596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_2581_, v_snd_2587_, v___x_2594_, v___x_2595_, v___x_2588_);
                    crate::leanh::lean_dec(v_snd_2587_);
                    v___x_2597_ = lean_nat_add(v___x_2592_, v___x_2596_);
                    crate::leanh::lean_dec(v___x_2596_);
                    return v___x_2597_;
                }
            } else {
                let mut v___x_2598_: usize = 0;
                let mut v___x_2599_: usize = 0;
                let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2598_ = 0usize;
                v___x_2599_ = lean_usize_of_nat(v___x_2589_);
                v___x_2600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_2581_, v_snd_2587_, v___x_2598_, v___x_2599_, v___x_2588_);
                crate::leanh::lean_dec(v_snd_2587_);
                v___x_2601_ = lean_nat_add(v___x_2592_, v___x_2600_);
                crate::leanh::lean_dec(v___x_2600_);
                return v___x_2601_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(
    mut v_state_2602_: *mut crate::leanh::LeanObject,
    mut v_as_2603_: *mut crate::leanh::LeanObject,
    mut v_i_2604_: usize,
    mut v_stop_2605_: usize,
    mut v_b_2606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2607_: u8 = 0;
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: u64 = 0;
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: usize = 0;
    let mut v___x_2613_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2607_ = lean_usize_dec_eq(v_i_2604_, v_stop_2605_);
                if v___x_2607_ == 0 {
                    v___x_2608_ = lean_array_uget_borrowed(v_as_2603_, v_i_2604_);
                    v___x_2609_ = crate::leanh::lean_unbox_uint64(v___x_2608_);
                    v___x_2610_ = l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(v_state_2602_, v___x_2609_);
                    v___x_2611_ = lean_nat_add(v_b_2606_, v___x_2610_);
                    crate::leanh::lean_dec(v___x_2610_);
                    crate::leanh::lean_dec(v_b_2606_);
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
    mut v_state_2615_: *mut crate::leanh::LeanObject,
    mut v_as_2616_: *mut crate::leanh::LeanObject,
    mut v_i_2617_: *mut crate::leanh::LeanObject,
    mut v_stop_2618_: *mut crate::leanh::LeanObject,
    mut v_b_2619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2620_: usize = 0;
    let mut v_stop_boxed_2621_: usize = 0;
    let mut v_res_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2620_ = crate::leanh::lean_unbox_usize(v_i_2617_);
    crate::leanh::lean_dec(v_i_2617_);
    v_stop_boxed_2621_ = crate::leanh::lean_unbox_usize(v_stop_2618_);
    crate::leanh::lean_dec(v_stop_2618_);
    v_res_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec_spec__0(v_state_2615_, v_as_2616_, v_i_boxed_2620_, v_stop_boxed_2621_, v_b_2619_);
    crate::leanh::lean_dec_ref(v_as_2616_);
    crate::leanh::lean_dec_ref(v_state_2615_);
    return v_res_2622_;
}
pub unsafe fn l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec___boxed(
    mut v_state_2623_: *mut crate::leanh::LeanObject,
    mut v_id_2624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_boxed_2625_: u64 = 0;
    let mut v_res_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_id_boxed_2625_ = crate::leanh::lean_unbox_uint64(v_id_2624_);
    crate::leanh::lean_dec_ref(v_id_2624_);
    v_res_2626_ =
        l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(
            v_state_2623_,
            v_id_boxed_2625_,
        );
    crate::leanh::lean_dec_ref(v_state_2623_);
    return v_res_2626_;
}
pub unsafe fn l_Std_CancellationContext_countAliveTokens___lam__0(
    mut v_id_2627_: u64,
    mut v___y_2628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2630_ = lean_st_ref_get(v___y_2628_);
    v___x_2631_ =
        l___private_Std_Sync_CancellationContext_0__Std_CancellationContext_countAliveTokensRec(
            v___x_2630_,
            v_id_2627_,
        );
    crate::leanh::lean_dec(v___x_2630_);
    return v___x_2631_;
}
pub unsafe fn l_Std_CancellationContext_countAliveTokens___lam__0___boxed(
    mut v_id_2632_: *mut crate::leanh::LeanObject,
    mut v___y_2633_: *mut crate::leanh::LeanObject,
    mut v___y_2634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_boxed_2635_: u64 = 0;
    let mut v_res_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_id_boxed_2635_ = crate::leanh::lean_unbox_uint64(v_id_2632_);
    crate::leanh::lean_dec_ref(v_id_2632_);
    v_res_2636_ =
        l_Std_CancellationContext_countAliveTokens___lam__0(v_id_boxed_2635_, v___y_2633_);
    crate::leanh::lean_dec(v___y_2633_);
    return v_res_2636_;
}
pub unsafe fn l_Std_CancellationContext_countAliveTokens(
    mut v_x_2637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_state_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_2640_: u64 = 0;
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_state_2639_ = crate::leanh::lean_ctor_get(v_x_2637_, 0);
    crate::leanh::lean_inc_ref(v_state_2639_);
    v_id_2640_ = crate::leanh::lean_ctor_get_uint64(
        v_x_2637_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    crate::leanh::lean_dec_ref(v_x_2637_);
    v___x_2641_ = crate::leanh::lean_box_uint64(v_id_2640_);
    v___f_2642_ = crate::leanh::lean_alloc_closure(
        l_Std_CancellationContext_countAliveTokens___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2642_, 0, v___x_2641_);
    v___x_2643_ = l_Std_Mutex_atomically___at___00Std_CancellationContext_fork_spec__1___redArg(
        v_state_2639_,
        v___f_2642_,
    );
    return v___x_2643_;
}
pub unsafe fn l_Std_CancellationContext_countAliveTokens___boxed(
    mut v_x_2644_: *mut crate::leanh::LeanObject,
    mut v_a_2645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2646_ = l_Std_CancellationContext_countAliveTokens(v_x_2644_);
    return v_res_2646_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sync_CancellationContext(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sync_CancellationToken(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_UInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_CancellationContext(
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
pub unsafe fn initialize_Std_Sync_CancellationContext(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sync_CancellationToken(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Ord_UInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_CancellationContext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sync_CancellationContext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Sync_CancellationContext(builtin);
}
