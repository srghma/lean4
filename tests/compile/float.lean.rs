// Lean compiler output
// Module: float
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::Data::UInt::BasicAux::*;
use lean_init::Init::Data::Repr::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
use lean_init::Init::Data::OfScientific::*;
use lean_init::Init::Data::Float::*;
use lean_init::Init::Data::List::Basic::*;
use lean_init::Init::Data::String::Defs::*;
use lean_init::Init::Data::Int::Basic::*;
use lean_init::Init::Prelude::*;
use lean_init::Init::Data::Nat::Log2::*;
use lean_init::Init::Data::Int::Repr::*;
extern "C" {
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_float_isinf(_: f64) -> u8;
    fn lean_float_frexp(_: f64) -> *mut lean_object;
    fn lean_float_isfinite(_: f64) -> u8;
    fn lean_float_isnan(_: f64) -> u8;
    fn lean_float_to_string(_: f64) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn pow(_: f64, _: f64) -> f64;
    fn lean_nat_pow(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_log2(_: *mut lean_object) -> *mut lean_object;
}
pub static l_IO_println___at___00tst1_spec__7___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_IO_println___at___00tst1_spec__7___closed__0: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00tst1_spec__7___closed__0_value) as *mut lean_object;
pub static l_IO_println___at___00tst1_spec__7___closed__1_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_IO_println___at___00tst1_spec__7___closed__1: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00tst1_spec__7___closed__1_value) as *mut lean_object;
pub static l_IO_println___at___00tst1_spec__7___closed__2_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_IO_println___at___00tst1_spec__7___closed__2: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00tst1_spec__7___closed__2_value) as *mut lean_object;
pub static l_IO_println___at___00tst1_spec__7___closed__3_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l_IO_println___at___00tst1_spec__7___closed__3: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00tst1_spec__7___closed__3_value) as *mut lean_object;
pub static l_IO_println___at___00tst1_spec__7___closed__4_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l_IO_println___at___00tst1_spec__7___closed__4: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00tst1_spec__7___closed__4_value) as *mut lean_object;
static mut l_tst1___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__0: f64 = 0.0;
static mut l_tst1___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__1: f64 = 0.0;
static mut l_tst1___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__2: f64 = 0.0;
static mut l_tst1___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__3: f64 = 0.0;
static mut l_tst1___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__4: f64 = 0.0;
static mut l_tst1___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__5: u8 = 0;
static mut l_tst1___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__6: u8 = 0;
static mut l_tst1___closed__7_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__7: u8 = 0;
static mut l_tst1___closed__8_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__8: f64 = 0.0;
static mut l_tst1___closed__9_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__9: f64 = 0.0;
static mut l_tst1___closed__10_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__10: f64 = 0.0;
static mut l_tst1___closed__11_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__11: u8 = 0;
static mut l_tst1___closed__12_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__12: u8 = 0;
static mut l_tst1___closed__13_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__13: u8 = 0;
static mut l_tst1___closed__14_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__14: u8 = 0;
static mut l_tst1___closed__15_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__15: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__16_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__16: f64 = 0.0;
static mut l_tst1___closed__17_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__17: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__18_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__18: f64 = 0.0;
static mut l_tst1___closed__19_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__19: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__20_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__20: f64 = 0.0;
static mut l_tst1___closed__21_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__21: f64 = 0.0;
static mut l_tst1___closed__22_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__22: f64 = 0.0;
static mut l_tst1___closed__23_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__23: f64 = 0.0;
static mut l_tst1___closed__24_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__24: u8 = 0;
static mut l_tst1___closed__25_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__25: u16 = 0;
static mut l_tst1___closed__26_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__26: u32 = 0;
static mut l_tst1___closed__27_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__27: u64 = 0;
static mut l_tst1___closed__28_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__28: usize = 0;
static mut l_tst1___closed__29_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__29: f64 = 0.0;
static mut l_tst1___closed__30_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__30: u8 = 0;
static mut l_tst1___closed__31_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__31: f64 = 0.0;
static mut l_tst1___closed__32_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__32: u8 = 0;
static mut l_tst1___closed__33_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__33: f64 = 0.0;
static mut l_tst1___closed__34_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__34: u8 = 0;
static mut l_tst1___closed__35_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__35: u16 = 0;
static mut l_tst1___closed__36_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__36: f64 = 0.0;
static mut l_tst1___closed__37_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__37: f64 = 0.0;
static mut l_tst1___closed__38_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__38: u16 = 0;
static mut l_tst1___closed__39_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__39: u16 = 0;
static mut l_tst1___closed__40_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__40: u32 = 0;
static mut l_tst1___closed__41_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__41: f64 = 0.0;
static mut l_tst1___closed__42_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__42: f64 = 0.0;
static mut l_tst1___closed__43_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__43: u32 = 0;
static mut l_tst1___closed__44_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__44: u32 = 0;
static mut l_tst1___closed__45_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__45: u64 = 0;
static mut l_tst1___closed__46_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__46: f64 = 0.0;
static mut l_tst1___closed__47_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__47: f64 = 0.0;
static mut l_tst1___closed__48_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__48: u64 = 0;
static mut l_tst1___closed__49_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__49: u64 = 0;
static mut l_tst1___closed__50_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__50: usize = 0;
static mut l_tst1___closed__51_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__51: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__52_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__52: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__53_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__53: f64 = 0.0;
static mut l_tst1___closed__54_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__54: f64 = 0.0;
static mut l_tst1___closed__55_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__55: usize = 0;
static mut l_tst1___closed__56_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__56: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__57_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__57: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__58_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__58: u8 = 0;
static mut l_tst1___closed__59_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__59: usize = 0;
static mut l_tst1___closed__60_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__60: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__61_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__61: u8 = 0;
static mut l_tst1___closed__62_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__62: f64 = 0.0;
static mut l_tst1___closed__63_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__63: u8 = 0;
static mut l_tst1___closed__64_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__64: u8 = 0;
static mut l_tst1___closed__65_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__65: u8 = 0;
static mut l_tst1___closed__66_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__66: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__67_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__67: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__68_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__68: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__69_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__69: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_tst1___closed__70___boxed__const__1: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__70_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__70: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__71_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__71: u8 = 0;
static mut l_tst1___closed__72_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__72: u8 = 0;
static mut l_tst1___closed__73_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__73: u8 = 0;
static mut l_tst1___closed__74_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__74: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__75_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__75: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__76_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__76: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__77_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__77: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_tst1___closed__78___boxed__const__1: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__78_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__78: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__79_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__79: f64 = 0.0;
static mut l_tst1___closed__80_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__80: f64 = 0.0;
static mut l_tst1___closed__81_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__81: u8 = 0;
static mut l_tst1___closed__82_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__82: u8 = 0;
static mut l_tst1___closed__83_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__83: u8 = 0;
static mut l_tst1___closed__84_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__84: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__85_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__85: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__86_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__86: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__87_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__87: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_tst1___closed__88___boxed__const__1: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__88_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__88: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__89_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__89: u8 = 0;
static mut l_tst1___closed__90_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__90: u8 = 0;
static mut l_tst1___closed__91_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__91: u8 = 0;
static mut l_tst1___closed__92_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__92: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__93_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__93: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__94_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__94: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__95_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__95: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_tst1___closed__96___boxed__const__1: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__96_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__96: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__97_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__97: f64 = 0.0;
static mut l_tst1___closed__98_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__98: u8 = 0;
static mut l_tst1___closed__99_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__99: u8 = 0;
static mut l_tst1___closed__100_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__100: u8 = 0;
static mut l_tst1___closed__101_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__101: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__102_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__102: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__103_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__103: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__104_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__104: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_tst1___closed__105___boxed__const__1: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__105_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__105: *mut lean_object = core::ptr::null_mut();
static mut l_tst1___closed__106_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__106: f64 = 0.0;
static mut l_tst1___closed__107_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__107: f64 = 0.0;
static mut l_tst1___closed__108_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_tst1___closed__108: f64 = 0.0;
pub static l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0___closed__0_value) as *mut lean_object;
pub static l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0___closed__1_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0___closed__1: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0___closed__1_value) as *mut lean_object;
pub static l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0___closed__2_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0___closed__2: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0___closed__2_value) as *mut lean_object;
pub static l_tst4___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_Float_abs___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_tst4___closed__0: *mut lean_object = core::ptr::addr_of!(l_tst4___closed__0_value) as *mut lean_object;
pub static l_main___closed__0_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [45, 45, 45, 45, 45, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: f64 = 0.0;
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: f64 = 0.0;
static mut l_main___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__3: f64 = 0.0;
static mut l_main___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__4: f64 = 0.0;
#[used]
#[no_mangle]
pub static mut l_main___closed__5___boxed__const__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__5: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_main___closed__6___boxed__const__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__6: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_main___closed__7___boxed__const__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__7_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__7: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_main___closed__8___boxed__const__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__8_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__8: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_main___closed__9___boxed__const__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__9_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__9: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_main___closed__10___boxed__const__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__10_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__10: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__11_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__11: f64 = 0.0;
static mut l_main___closed__12_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__12: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__13_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__13: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_main___closed__14___boxed__const__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__14_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__14: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_main___closed__15___boxed__const__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__15_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__15: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_main___closed__16___boxed__const__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__16_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__16: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__17_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__17: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00tst1_spec__0_spec__0(mut v_s_1_: *mut lean_object) -> *mut lean_object{
let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_3_ = lean_get_stdout();
v_putStr_4_ = lean_ctor_get(v___x_3_, 4);
lean_inc_ref(v_putStr_4_);
lean_dec_ref(v___x_3_);
v___x_5_ = lean_apply_2(v_putStr_4_, v_s_1_, lean_box(0));
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00tst1_spec__0_spec__0___boxed(mut v_s_6_: *mut lean_object, mut v_a_7_: *mut lean_object) -> *mut lean_object{
let mut v_res_8_: *mut lean_object = core::ptr::null_mut(); 
v_res_8_ = l_IO_print___at___00IO_println___at___00tst1_spec__0_spec__0(v_s_6_);
return v_res_8_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst1_spec__3(mut v_s_9_: u16) -> *mut lean_object{
let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: u32 = 0; let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); 
v___x_11_ = lean_uint16_to_nat(v_s_9_);
v___x_12_ = l_Nat_reprFast(v___x_11_);
v___x_13_ = 10;
v___x_14_ = lean_string_push(v___x_12_, v___x_13_);
v___x_15_ = l_IO_print___at___00IO_println___at___00tst1_spec__0_spec__0(v___x_14_);
return v___x_15_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst1_spec__3___boxed(mut v_s_16_: *mut lean_object, mut v_a_17_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_18_: u16 = 0; let mut v_res_19_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_18_ = (lean_unbox(v_s_16_) as u16);
v_res_19_ = l_IO_println___at___00tst1_spec__3(v_s_boxed_18_);
return v_res_19_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst1_spec__6(mut v_s_20_: usize) -> *mut lean_object{
let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: u32 = 0; let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); 
v___x_22_ = lean_usize_to_nat(v_s_20_);
v___x_23_ = l_Nat_reprFast(v___x_22_);
v___x_24_ = 10;
v___x_25_ = lean_string_push(v___x_23_, v___x_24_);
v___x_26_ = l_IO_print___at___00IO_println___at___00tst1_spec__0_spec__0(v___x_25_);
return v___x_26_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst1_spec__6___boxed(mut v_s_27_: *mut lean_object, mut v_a_28_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_29_: usize = 0; let mut v_res_30_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_29_ = lean_unbox_usize(v_s_27_);
lean_dec(v_s_27_);
v_res_30_ = l_IO_println___at___00tst1_spec__6(v_s_boxed_29_);
return v_res_30_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst1_spec__4(mut v_s_31_: u32) -> *mut lean_object{
let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: u32 = 0; let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); 
v___x_33_ = lean_uint32_to_nat(v_s_31_);
v___x_34_ = l_Nat_reprFast(v___x_33_);
v___x_35_ = 10;
v___x_36_ = lean_string_push(v___x_34_, v___x_35_);
v___x_37_ = l_IO_print___at___00IO_println___at___00tst1_spec__0_spec__0(v___x_36_);
return v___x_37_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst1_spec__4___boxed(mut v_s_38_: *mut lean_object, mut v_a_39_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_40_: u32 = 0; let mut v_res_41_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_40_ = lean_unbox_uint32(v_s_38_);
lean_dec(v_s_38_);
v_res_41_ = l_IO_println___at___00tst1_spec__4(v_s_boxed_40_);
return v_res_41_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst1_spec__5(mut v_s_42_: u64) -> *mut lean_object{
let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); let mut v___x_46_: u32 = 0; let mut v___x_47_: *mut lean_object = core::ptr::null_mut(); let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); 
v___x_44_ = lean_uint64_to_nat(v_s_42_);
v___x_45_ = l_Nat_reprFast(v___x_44_);
v___x_46_ = 10;
v___x_47_ = lean_string_push(v___x_45_, v___x_46_);
v___x_48_ = l_IO_print___at___00IO_println___at___00tst1_spec__0_spec__0(v___x_47_);
return v___x_48_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst1_spec__5___boxed(mut v_s_49_: *mut lean_object, mut v_a_50_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_51_: u64 = 0; let mut v_res_52_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_51_ = lean_unbox_uint64(v_s_49_);
lean_dec_ref(v_s_49_);
v_res_52_ = l_IO_println___at___00tst1_spec__5(v_s_boxed_51_);
return v_res_52_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst1_spec__2(mut v_s_53_: u8) -> *mut lean_object{
let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); let mut v___x_57_: u32 = 0; let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); 
v___x_55_ = lean_uint8_to_nat(v_s_53_);
v___x_56_ = l_Nat_reprFast(v___x_55_);
v___x_57_ = 10;
v___x_58_ = lean_string_push(v___x_56_, v___x_57_);
v___x_59_ = l_IO_print___at___00IO_println___at___00tst1_spec__0_spec__0(v___x_58_);
return v___x_59_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst1_spec__2___boxed(mut v_s_60_: *mut lean_object, mut v_a_61_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_62_: u8 = 0; let mut v_res_63_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_62_ = (lean_unbox(v_s_60_) as u8);
v_res_63_ = l_IO_println___at___00tst1_spec__2(v_s_boxed_62_);
return v_res_63_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst1_spec__7(mut v_s_69_: *mut lean_object) -> *mut lean_object{
let mut v_snd_71_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_72_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_73_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_74_: *mut lean_object = core::ptr::null_mut(); let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); let mut v___x_76_: f64 = 0.0; let mut v___x_77_: *mut lean_object = core::ptr::null_mut(); let mut v___x_78_: *mut lean_object = core::ptr::null_mut(); let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); let mut v___y_82_: *mut lean_object = core::ptr::null_mut(); let mut v___y_83_: *mut lean_object = core::ptr::null_mut(); let mut v___y_84_: *mut lean_object = core::ptr::null_mut(); let mut v___y_85_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_86_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_87_: *mut lean_object = core::ptr::null_mut(); let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: f64 = 0.0; let mut v___x_91_: *mut lean_object = core::ptr::null_mut(); let mut v___x_92_: *mut lean_object = core::ptr::null_mut(); let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); let mut v___x_94_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v___x_98_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_106_: u32 = 0; let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); let mut v___x_108_: *mut lean_object = core::ptr::null_mut(); let mut v___y_110_: *mut lean_object = core::ptr::null_mut(); let mut v___y_111_: *mut lean_object = core::ptr::null_mut(); let mut v___y_112_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_113_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_114_: *mut lean_object = core::ptr::null_mut(); let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: u8 = 0; let mut v___x_118_: *mut lean_object = core::ptr::null_mut(); let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); let mut v___y_121_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_122_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_123_: *mut lean_object = core::ptr::null_mut(); let mut v___x_124_: *mut lean_object = core::ptr::null_mut(); let mut v___x_125_: *mut lean_object = core::ptr::null_mut(); let mut v___x_126_: u8 = 0; let mut v___x_127_: *mut lean_object = core::ptr::null_mut(); let mut v___x_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_129_: u8 = 0; let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_snd_71_ = lean_ctor_get(v_s_69_, 1);
v_fst_72_ = lean_ctor_get(v_s_69_, 0);
v_fst_73_ = lean_ctor_get(v_snd_71_, 0);
v_snd_74_ = lean_ctor_get(v_snd_71_, 1);
v___x_75_ = l_IO_println___at___00tst1_spec__7___closed__0;
v___x_76_ = lean_unbox_float(v_fst_72_);
v___x_77_ = lean_float_to_string(v___x_76_);
v___x_78_ = lean_string_append(v___x_75_, v___x_77_);
lean_dec_ref(v___x_77_);
v___x_79_ = l_IO_println___at___00tst1_spec__7___closed__1;
v___x_80_ = lean_string_append(v___x_78_, v___x_79_);
v___x_129_ = (lean_unbox(v_fst_73_) as u8);
if v___x_129_ == 0 {
v___x_130_ = l_IO_println___at___00tst1_spec__7___closed__3;
v___y_121_ = v___x_130_;
state = 3; continue;
} else {
v___x_131_ = l_IO_println___at___00tst1_spec__7___closed__4;
v___y_121_ = v___x_131_;
state = 3; continue;
}
}
1 => {
v_fst_86_ = lean_ctor_get(v___y_84_, 0);
v_snd_87_ = lean_ctor_get(v___y_84_, 1);
v___x_88_ = lean_string_append(v___x_75_, v___y_85_);
v___x_89_ = lean_string_append(v___x_88_, v___x_79_);
v___x_90_ = lean_unbox_float(v_fst_86_);
v___x_91_ = lean_float_to_string(v___x_90_);
v___x_92_ = lean_string_append(v___x_75_, v___x_91_);
lean_dec_ref(v___x_91_);
v___x_93_ = lean_string_append(v___x_92_, v___x_79_);
v___x_94_ = l_Int_repr(v_snd_87_);
v___x_95_ = lean_string_append(v___x_93_, v___x_94_);
lean_dec_ref(v___x_94_);
v___x_96_ = l_IO_println___at___00tst1_spec__7___closed__2;
v___x_97_ = lean_string_append(v___x_95_, v___x_96_);
v___x_98_ = lean_string_append(v___x_89_, v___x_97_);
lean_dec_ref(v___x_97_);
v___x_99_ = lean_string_append(v___x_98_, v___x_96_);
v___x_100_ = lean_string_append(v___y_82_, v___x_99_);
lean_dec_ref(v___x_99_);
v___x_101_ = lean_string_append(v___x_100_, v___x_96_);
v___x_102_ = lean_string_append(v___y_83_, v___x_101_);
lean_dec_ref(v___x_101_);
v___x_103_ = lean_string_append(v___x_102_, v___x_96_);
v___x_104_ = lean_string_append(v___x_80_, v___x_103_);
lean_dec_ref(v___x_103_);
v___x_105_ = lean_string_append(v___x_104_, v___x_96_);
v___x_106_ = 10;
v___x_107_ = lean_string_push(v___x_105_, v___x_106_);
v___x_108_ = l_IO_print___at___00IO_println___at___00tst1_spec__0_spec__0(v___x_107_);
return v___x_108_;
}
2 => {
v_fst_113_ = lean_ctor_get(v___y_111_, 0);
v_snd_114_ = lean_ctor_get(v___y_111_, 1);
v___x_115_ = lean_string_append(v___x_75_, v___y_112_);
v___x_116_ = lean_string_append(v___x_115_, v___x_79_);
v___x_117_ = (lean_unbox(v_fst_113_) as u8);
if v___x_117_ == 0 {
v___x_118_ = l_IO_println___at___00tst1_spec__7___closed__3;
v___y_82_ = v___x_116_;
v___y_83_ = v___y_110_;
v___y_84_ = v_snd_114_;
v___y_85_ = v___x_118_;
state = 1; continue;
} else {
v___x_119_ = l_IO_println___at___00tst1_spec__7___closed__4;
v___y_82_ = v___x_116_;
v___y_83_ = v___y_110_;
v___y_84_ = v_snd_114_;
v___y_85_ = v___x_119_;
state = 1; continue;
}
}
3 => {
v_fst_122_ = lean_ctor_get(v_snd_74_, 0);
v_snd_123_ = lean_ctor_get(v_snd_74_, 1);
v___x_124_ = lean_string_append(v___x_75_, v___y_121_);
v___x_125_ = lean_string_append(v___x_124_, v___x_79_);
v___x_126_ = (lean_unbox(v_fst_122_) as u8);
if v___x_126_ == 0 {
v___x_127_ = l_IO_println___at___00tst1_spec__7___closed__3;
v___y_110_ = v___x_125_;
v___y_111_ = v_snd_123_;
v___y_112_ = v___x_127_;
state = 2; continue;
} else {
v___x_128_ = l_IO_println___at___00tst1_spec__7___closed__4;
v___y_110_ = v___x_125_;
v___y_111_ = v_snd_123_;
v___y_112_ = v___x_128_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst1_spec__7___boxed(mut v_s_132_: *mut lean_object, mut v_a_133_: *mut lean_object) -> *mut lean_object{
let mut v_res_134_: *mut lean_object = core::ptr::null_mut(); 
v_res_134_ = l_IO_println___at___00tst1_spec__7(v_s_132_);
lean_dec_ref(v_s_132_);
return v_res_134_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst1_spec__1(mut v_s_135_: u8) -> *mut lean_object{
let mut v___y_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_139_: u32 = 0; let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_143_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if v_s_135_ == 0 {
v___x_142_ = l_IO_println___at___00tst1_spec__7___closed__3;
v___y_138_ = v___x_142_;
state = 1; continue;
} else {
v___x_143_ = l_IO_println___at___00tst1_spec__7___closed__4;
v___y_138_ = v___x_143_;
state = 1; continue;
}
}
1 => {
v___x_139_ = 10;
lean_inc_ref(v___y_138_);
v___x_140_ = lean_string_push(v___y_138_, v___x_139_);
v___x_141_ = l_IO_print___at___00IO_println___at___00tst1_spec__0_spec__0(v___x_140_);
return v___x_141_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst1_spec__1___boxed(mut v_s_144_: *mut lean_object, mut v_a_145_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_146_: u8 = 0; let mut v_res_147_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_146_ = (lean_unbox(v_s_144_) as u8);
v_res_147_ = l_IO_println___at___00tst1_spec__1(v_s_boxed_146_);
return v_res_147_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst1_spec__0(mut v_s_148_: f64) -> *mut lean_object{
let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); let mut v___x_151_: u32 = 0; let mut v___x_152_: *mut lean_object = core::ptr::null_mut(); let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); 
v___x_150_ = lean_float_to_string(v_s_148_);
v___x_151_ = 10;
v___x_152_ = lean_string_push(v___x_150_, v___x_151_);
v___x_153_ = l_IO_print___at___00IO_println___at___00tst1_spec__0_spec__0(v___x_152_);
return v___x_153_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst1_spec__0___boxed(mut v_s_154_: *mut lean_object, mut v_a_155_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_156_: f64 = 0.0; let mut v_res_157_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_156_ = lean_unbox_float(v_s_154_);
lean_dec_ref(v_s_154_);
v_res_157_ = l_IO_println___at___00tst1_spec__0(v_s_boxed_156_);
return v_res_157_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__0() -> f64{
let mut v___x_158_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: f64 = 0.0; 
v___x_158_ = lean_unsigned_to_nat(1);
v___x_159_ = lean_float_of_nat(v___x_158_);
return v___x_159_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__1() -> f64{
let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_161_: f64 = 0.0; 
v___x_160_ = lean_unsigned_to_nat(2);
v___x_161_ = lean_float_of_nat(v___x_160_);
return v___x_161_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__2() -> f64{
let mut v___x_162_: f64 = 0.0; let mut v___x_163_: f64 = 0.0; let mut v___x_164_: f64 = 0.0; 
v___x_162_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__1), core::ptr::addr_of_mut!(l_tst1___closed__1_once), _init_l_tst1___closed__1);
v___x_163_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__0), core::ptr::addr_of_mut!(l_tst1___closed__0_once), _init_l_tst1___closed__0);
v___x_164_ = lean_float_add(v___x_163_, v___x_162_);
return v___x_164_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__3() -> f64{
let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); let mut v___x_166_: f64 = 0.0; 
v___x_165_ = lean_unsigned_to_nat(3);
v___x_166_ = lean_float_of_nat(v___x_165_);
return v___x_166_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__4() -> f64{
let mut v___x_167_: f64 = 0.0; let mut v___x_168_: f64 = 0.0; let mut v___x_169_: f64 = 0.0; 
v___x_167_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__3), core::ptr::addr_of_mut!(l_tst1___closed__3_once), _init_l_tst1___closed__3);
v___x_168_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__1), core::ptr::addr_of_mut!(l_tst1___closed__1_once), _init_l_tst1___closed__1);
v___x_169_ = lean_float_sub(v___x_168_, v___x_167_);
return v___x_169_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__5() -> u8{
let mut v___x_170_: f64 = 0.0; let mut v___x_171_: f64 = 0.0; let mut v___x_172_: u8 = 0; 
v___x_170_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__1), core::ptr::addr_of_mut!(l_tst1___closed__1_once), _init_l_tst1___closed__1);
v___x_171_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__3), core::ptr::addr_of_mut!(l_tst1___closed__3_once), _init_l_tst1___closed__3);
v___x_172_ = lean_float_decLt(v___x_171_, v___x_170_);
return v___x_172_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__6() -> u8{
let mut v___x_173_: f64 = 0.0; let mut v___x_174_: f64 = 0.0; let mut v___x_175_: u8 = 0; 
v___x_173_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__1), core::ptr::addr_of_mut!(l_tst1___closed__1_once), _init_l_tst1___closed__1);
v___x_174_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__3), core::ptr::addr_of_mut!(l_tst1___closed__3_once), _init_l_tst1___closed__3);
v___x_175_ = lean_float_decLe(v___x_174_, v___x_173_);
return v___x_175_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__7() -> u8{
let mut v___x_176_: f64 = 0.0; let mut v___x_177_: u8 = 0; 
v___x_176_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__3), core::ptr::addr_of_mut!(l_tst1___closed__3_once), _init_l_tst1___closed__3);
v___x_177_ = lean_float_decLe(v___x_176_, v___x_176_);
return v___x_177_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__8() -> f64{
let mut v___x_178_: f64 = 0.0; let mut v___x_179_: f64 = 0.0; let mut v___x_180_: f64 = 0.0; 
v___x_178_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__1), core::ptr::addr_of_mut!(l_tst1___closed__1_once), _init_l_tst1___closed__1);
v___x_179_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__3), core::ptr::addr_of_mut!(l_tst1___closed__3_once), _init_l_tst1___closed__3);
v___x_180_ = lean_float_mul(v___x_179_, v___x_178_);
return v___x_180_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__9() -> f64{
let mut v___x_181_: f64 = 0.0; let mut v___x_182_: f64 = 0.0; let mut v___x_183_: f64 = 0.0; 
v___x_181_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__1), core::ptr::addr_of_mut!(l_tst1___closed__1_once), _init_l_tst1___closed__1);
v___x_182_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__3), core::ptr::addr_of_mut!(l_tst1___closed__3_once), _init_l_tst1___closed__3);
v___x_183_ = lean_float_div(v___x_182_, v___x_181_);
return v___x_183_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__10() -> f64{
let mut v___x_184_: *mut lean_object = core::ptr::null_mut(); let mut v___x_185_: f64 = 0.0; 
v___x_184_ = lean_unsigned_to_nat(4);
v___x_185_ = lean_float_of_nat(v___x_184_);
return v___x_185_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__11() -> u8{
let mut v___x_186_: f64 = 0.0; let mut v___x_187_: f64 = 0.0; let mut v___x_188_: u8 = 0; 
v___x_186_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__10), core::ptr::addr_of_mut!(l_tst1___closed__10_once), _init_l_tst1___closed__10);
v___x_187_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__3), core::ptr::addr_of_mut!(l_tst1___closed__3_once), _init_l_tst1___closed__3);
v___x_188_ = lean_float_decLt(v___x_187_, v___x_186_);
return v___x_188_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__12() -> u8{
let mut v___x_189_: f64 = 0.0; let mut v___x_190_: f64 = 0.0; let mut v___x_191_: u8 = 0; 
v___x_189_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__10), core::ptr::addr_of_mut!(l_tst1___closed__10_once), _init_l_tst1___closed__10);
v___x_190_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__3), core::ptr::addr_of_mut!(l_tst1___closed__3_once), _init_l_tst1___closed__3);
v___x_191_ = lean_float_decLe(v___x_190_, v___x_189_);
return v___x_191_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__13() -> u8{
let mut v___x_192_: f64 = 0.0; let mut v___x_193_: f64 = 0.0; let mut v___x_194_: u8 = 0; 
v___x_192_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__1), core::ptr::addr_of_mut!(l_tst1___closed__1_once), _init_l_tst1___closed__1);
v___x_193_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__3), core::ptr::addr_of_mut!(l_tst1___closed__3_once), _init_l_tst1___closed__3);
v___x_194_ = lean_float_beq(v___x_193_, v___x_192_);
return v___x_194_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__14() -> u8{
let mut v___x_195_: f64 = 0.0; let mut v___x_196_: u8 = 0; 
v___x_195_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__1), core::ptr::addr_of_mut!(l_tst1___closed__1_once), _init_l_tst1___closed__1);
v___x_196_ = lean_float_beq(v___x_195_, v___x_195_);
return v___x_196_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__15() -> *mut lean_object{
let mut v___x_197_: *mut lean_object = core::ptr::null_mut(); let mut v___x_198_: *mut lean_object = core::ptr::null_mut(); 
v___x_197_ = lean_unsigned_to_nat(0);
v___x_198_ = lean_nat_to_int(v___x_197_);
return v___x_198_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__16() -> f64{
let mut v___x_199_: *mut lean_object = core::ptr::null_mut(); let mut v___x_200_: f64 = 0.0; 
v___x_199_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__15), core::ptr::addr_of_mut!(l_tst1___closed__15_once), _init_l_tst1___closed__15);
v___x_200_ = l_Float_ofInt(v___x_199_);
return v___x_200_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__17() -> *mut lean_object{
let mut v___x_201_: *mut lean_object = core::ptr::null_mut(); let mut v___x_202_: *mut lean_object = core::ptr::null_mut(); 
v___x_201_ = lean_unsigned_to_nat(42);
v___x_202_ = lean_nat_to_int(v___x_201_);
return v___x_202_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__18() -> f64{
let mut v___x_203_: *mut lean_object = core::ptr::null_mut(); let mut v___x_204_: f64 = 0.0; 
v___x_203_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__17), core::ptr::addr_of_mut!(l_tst1___closed__17_once), _init_l_tst1___closed__17);
v___x_204_ = l_Float_ofInt(v___x_203_);
return v___x_204_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__19() -> *mut lean_object{
let mut v___x_205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_206_: *mut lean_object = core::ptr::null_mut(); 
v___x_205_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__17), core::ptr::addr_of_mut!(l_tst1___closed__17_once), _init_l_tst1___closed__17);
v___x_206_ = lean_int_neg(v___x_205_);
return v___x_206_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__20() -> f64{
let mut v___x_207_: *mut lean_object = core::ptr::null_mut(); let mut v___x_208_: f64 = 0.0; 
v___x_207_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__19), core::ptr::addr_of_mut!(l_tst1___closed__19_once), _init_l_tst1___closed__19);
v___x_208_ = l_Float_ofInt(v___x_207_);
return v___x_208_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__21() -> f64{
let mut v___x_209_: u64 = 0; let mut v___x_210_: f64 = 0.0; 
v___x_209_ = 0u64;
v___x_210_ = lean_uint64_to_float(v___x_209_);
return v___x_210_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__22() -> f64{
let mut v___x_211_: *mut lean_object = core::ptr::null_mut(); let mut v___x_212_: f64 = 0.0; 
v___x_211_ = lean_unsigned_to_nat(0);
v___x_212_ = lean_float_of_nat(v___x_211_);
return v___x_212_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__23() -> f64{
let mut v___x_213_: f64 = 0.0; let mut v___x_214_: f64 = 0.0; 
v___x_213_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__22), core::ptr::addr_of_mut!(l_tst1___closed__22_once), _init_l_tst1___closed__22);
v___x_214_ = lean_float_div(v___x_213_, v___x_213_);
return v___x_214_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__24() -> u8{
let mut v___x_215_: f64 = 0.0; let mut v___x_216_: u8 = 0; 
v___x_215_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__23), core::ptr::addr_of_mut!(l_tst1___closed__23_once), _init_l_tst1___closed__23);
v___x_216_ = lean_float_to_uint8(v___x_215_);
return v___x_216_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__25() -> u16{
let mut v___x_217_: f64 = 0.0; let mut v___x_218_: u16 = 0; 
v___x_217_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__23), core::ptr::addr_of_mut!(l_tst1___closed__23_once), _init_l_tst1___closed__23);
v___x_218_ = lean_float_to_uint16(v___x_217_);
return v___x_218_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__26() -> u32{
let mut v___x_219_: f64 = 0.0; let mut v___x_220_: u32 = 0; 
v___x_219_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__23), core::ptr::addr_of_mut!(l_tst1___closed__23_once), _init_l_tst1___closed__23);
v___x_220_ = lean_float_to_uint32(v___x_219_);
return v___x_220_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__27() -> u64{
let mut v___x_221_: f64 = 0.0; let mut v___x_222_: u64 = 0; 
v___x_221_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__23), core::ptr::addr_of_mut!(l_tst1___closed__23_once), _init_l_tst1___closed__23);
v___x_222_ = lean_float_to_uint64(v___x_221_);
return v___x_222_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__28() -> usize{
let mut v___x_223_: f64 = 0.0; let mut v___x_224_: usize = 0; 
v___x_223_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__23), core::ptr::addr_of_mut!(l_tst1___closed__23_once), _init_l_tst1___closed__23);
v___x_224_ = lean_float_to_usize(v___x_223_);
return v___x_224_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__29() -> f64{
let mut v___x_225_: f64 = 0.0; let mut v___x_226_: f64 = 0.0; 
v___x_225_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__0), core::ptr::addr_of_mut!(l_tst1___closed__0_once), _init_l_tst1___closed__0);
v___x_226_ = lean_float_negate(v___x_225_);
return v___x_226_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__30() -> u8{
let mut v___x_227_: f64 = 0.0; let mut v___x_228_: u8 = 0; 
v___x_227_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__29), core::ptr::addr_of_mut!(l_tst1___closed__29_once), _init_l_tst1___closed__29);
v___x_228_ = lean_float_to_uint8(v___x_227_);
return v___x_228_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__31() -> f64{
let mut v___x_229_: *mut lean_object = core::ptr::null_mut(); let mut v___x_230_: f64 = 0.0; 
v___x_229_ = lean_unsigned_to_nat(256);
v___x_230_ = lean_float_of_nat(v___x_229_);
return v___x_230_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__32() -> u8{
let mut v___x_231_: f64 = 0.0; let mut v___x_232_: u8 = 0; 
v___x_231_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__31), core::ptr::addr_of_mut!(l_tst1___closed__31_once), _init_l_tst1___closed__31);
v___x_232_ = lean_float_to_uint8(v___x_231_);
return v___x_232_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__33() -> f64{
let mut v___x_233_: f64 = 0.0; let mut v___x_234_: f64 = 0.0; let mut v___x_235_: f64 = 0.0; 
v___x_233_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__22), core::ptr::addr_of_mut!(l_tst1___closed__22_once), _init_l_tst1___closed__22);
v___x_234_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__0), core::ptr::addr_of_mut!(l_tst1___closed__0_once), _init_l_tst1___closed__0);
v___x_235_ = lean_float_div(v___x_234_, v___x_233_);
return v___x_235_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__34() -> u8{
let mut v___x_236_: f64 = 0.0; let mut v___x_237_: u8 = 0; 
v___x_236_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__33), core::ptr::addr_of_mut!(l_tst1___closed__33_once), _init_l_tst1___closed__33);
v___x_237_ = lean_float_to_uint8(v___x_236_);
return v___x_237_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__35() -> u16{
let mut v___x_238_: f64 = 0.0; let mut v___x_239_: u16 = 0; 
v___x_238_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__29), core::ptr::addr_of_mut!(l_tst1___closed__29_once), _init_l_tst1___closed__29);
v___x_239_ = lean_float_to_uint16(v___x_238_);
return v___x_239_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__36() -> f64{
let mut v___x_240_: *mut lean_object = core::ptr::null_mut(); let mut v___x_241_: f64 = 0.0; 
v___x_240_ = lean_unsigned_to_nat(16);
v___x_241_ = lean_float_of_nat(v___x_240_);
return v___x_241_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__37() -> f64{
let mut v___x_242_: f64 = 0.0; let mut v___x_243_: f64 = 0.0; let mut v___x_244_: f64 = 0.0; 
v___x_242_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__36), core::ptr::addr_of_mut!(l_tst1___closed__36_once), _init_l_tst1___closed__36);
v___x_243_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__1), core::ptr::addr_of_mut!(l_tst1___closed__1_once), _init_l_tst1___closed__1);
v___x_244_ = pow(v___x_243_, v___x_242_);
return v___x_244_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__38() -> u16{
let mut v___x_245_: f64 = 0.0; let mut v___x_246_: u16 = 0; 
v___x_245_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__37), core::ptr::addr_of_mut!(l_tst1___closed__37_once), _init_l_tst1___closed__37);
v___x_246_ = lean_float_to_uint16(v___x_245_);
return v___x_246_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__39() -> u16{
let mut v___x_247_: f64 = 0.0; let mut v___x_248_: u16 = 0; 
v___x_247_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__33), core::ptr::addr_of_mut!(l_tst1___closed__33_once), _init_l_tst1___closed__33);
v___x_248_ = lean_float_to_uint16(v___x_247_);
return v___x_248_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__40() -> u32{
let mut v___x_249_: f64 = 0.0; let mut v___x_250_: u32 = 0; 
v___x_249_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__29), core::ptr::addr_of_mut!(l_tst1___closed__29_once), _init_l_tst1___closed__29);
v___x_250_ = lean_float_to_uint32(v___x_249_);
return v___x_250_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__41() -> f64{
let mut v___x_251_: *mut lean_object = core::ptr::null_mut(); let mut v___x_252_: f64 = 0.0; 
v___x_251_ = lean_unsigned_to_nat(32);
v___x_252_ = lean_float_of_nat(v___x_251_);
return v___x_252_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__42() -> f64{
let mut v___x_253_: f64 = 0.0; let mut v___x_254_: f64 = 0.0; let mut v___x_255_: f64 = 0.0; 
v___x_253_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__41), core::ptr::addr_of_mut!(l_tst1___closed__41_once), _init_l_tst1___closed__41);
v___x_254_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__1), core::ptr::addr_of_mut!(l_tst1___closed__1_once), _init_l_tst1___closed__1);
v___x_255_ = pow(v___x_254_, v___x_253_);
return v___x_255_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__43() -> u32{
let mut v___x_256_: f64 = 0.0; let mut v___x_257_: u32 = 0; 
v___x_256_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__42), core::ptr::addr_of_mut!(l_tst1___closed__42_once), _init_l_tst1___closed__42);
v___x_257_ = lean_float_to_uint32(v___x_256_);
return v___x_257_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__44() -> u32{
let mut v___x_258_: f64 = 0.0; let mut v___x_259_: u32 = 0; 
v___x_258_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__33), core::ptr::addr_of_mut!(l_tst1___closed__33_once), _init_l_tst1___closed__33);
v___x_259_ = lean_float_to_uint32(v___x_258_);
return v___x_259_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__45() -> u64{
let mut v___x_260_: f64 = 0.0; let mut v___x_261_: u64 = 0; 
v___x_260_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__29), core::ptr::addr_of_mut!(l_tst1___closed__29_once), _init_l_tst1___closed__29);
v___x_261_ = lean_float_to_uint64(v___x_260_);
return v___x_261_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__46() -> f64{
let mut v___x_262_: *mut lean_object = core::ptr::null_mut(); let mut v___x_263_: f64 = 0.0; 
v___x_262_ = lean_unsigned_to_nat(64);
v___x_263_ = lean_float_of_nat(v___x_262_);
return v___x_263_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__47() -> f64{
let mut v___x_264_: f64 = 0.0; let mut v___x_265_: f64 = 0.0; let mut v___x_266_: f64 = 0.0; 
v___x_264_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__46), core::ptr::addr_of_mut!(l_tst1___closed__46_once), _init_l_tst1___closed__46);
v___x_265_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__1), core::ptr::addr_of_mut!(l_tst1___closed__1_once), _init_l_tst1___closed__1);
v___x_266_ = pow(v___x_265_, v___x_264_);
return v___x_266_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__48() -> u64{
let mut v___x_267_: f64 = 0.0; let mut v___x_268_: u64 = 0; 
v___x_267_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__47), core::ptr::addr_of_mut!(l_tst1___closed__47_once), _init_l_tst1___closed__47);
v___x_268_ = lean_float_to_uint64(v___x_267_);
return v___x_268_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__49() -> u64{
let mut v___x_269_: f64 = 0.0; let mut v___x_270_: u64 = 0; 
v___x_269_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__33), core::ptr::addr_of_mut!(l_tst1___closed__33_once), _init_l_tst1___closed__33);
v___x_270_ = lean_float_to_uint64(v___x_269_);
return v___x_270_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__50() -> usize{
let mut v___x_271_: f64 = 0.0; let mut v___x_272_: usize = 0; 
v___x_271_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__29), core::ptr::addr_of_mut!(l_tst1___closed__29_once), _init_l_tst1___closed__29);
v___x_272_ = lean_float_to_usize(v___x_271_);
return v___x_272_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__51() -> *mut lean_object{
let mut v___x_273_: *mut lean_object = core::ptr::null_mut(); let mut v___x_274_: *mut lean_object = core::ptr::null_mut(); let mut v___x_275_: *mut lean_object = core::ptr::null_mut(); 
v___x_273_ = l_System_Platform_numBits;
v___x_274_ = lean_unsigned_to_nat(2);
v___x_275_ = lean_nat_pow(v___x_274_, v___x_273_);
return v___x_275_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__52() -> *mut lean_object{
let mut v___x_276_: *mut lean_object = core::ptr::null_mut(); let mut v___x_277_: *mut lean_object = core::ptr::null_mut(); 
v___x_276_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__51), core::ptr::addr_of_mut!(l_tst1___closed__51_once), _init_l_tst1___closed__51);
v___x_277_ = lean_nat_log2(v___x_276_);
return v___x_277_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__53() -> f64{
let mut v___x_278_: *mut lean_object = core::ptr::null_mut(); let mut v___x_279_: f64 = 0.0; 
v___x_278_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__52), core::ptr::addr_of_mut!(l_tst1___closed__52_once), _init_l_tst1___closed__52);
v___x_279_ = lean_float_of_nat(v___x_278_);
return v___x_279_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__54() -> f64{
let mut v___x_280_: f64 = 0.0; let mut v___x_281_: f64 = 0.0; let mut v___x_282_: f64 = 0.0; 
v___x_280_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__53), core::ptr::addr_of_mut!(l_tst1___closed__53_once), _init_l_tst1___closed__53);
v___x_281_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__1), core::ptr::addr_of_mut!(l_tst1___closed__1_once), _init_l_tst1___closed__1);
v___x_282_ = pow(v___x_281_, v___x_280_);
return v___x_282_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__55() -> usize{
let mut v___x_283_: f64 = 0.0; let mut v___x_284_: usize = 0; 
v___x_283_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__54), core::ptr::addr_of_mut!(l_tst1___closed__54_once), _init_l_tst1___closed__54);
v___x_284_ = lean_float_to_usize(v___x_283_);
return v___x_284_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__56() -> *mut lean_object{
let mut v___x_285_: usize = 0; let mut v___x_286_: *mut lean_object = core::ptr::null_mut(); 
v___x_285_ = lean_usize_once(core::ptr::addr_of_mut!(l_tst1___closed__55), core::ptr::addr_of_mut!(l_tst1___closed__55_once), _init_l_tst1___closed__55);
v___x_286_ = lean_usize_to_nat(v___x_285_);
return v___x_286_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__57() -> *mut lean_object{
let mut v___x_287_: *mut lean_object = core::ptr::null_mut(); let mut v___x_288_: *mut lean_object = core::ptr::null_mut(); let mut v___x_289_: *mut lean_object = core::ptr::null_mut(); 
v___x_287_ = lean_unsigned_to_nat(1);
v___x_288_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__51), core::ptr::addr_of_mut!(l_tst1___closed__51_once), _init_l_tst1___closed__51);
v___x_289_ = lean_nat_sub(v___x_288_, v___x_287_);
return v___x_289_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__58() -> u8{
let mut v___x_290_: *mut lean_object = core::ptr::null_mut(); let mut v___x_291_: *mut lean_object = core::ptr::null_mut(); let mut v___x_292_: u8 = 0; 
v___x_290_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__57), core::ptr::addr_of_mut!(l_tst1___closed__57_once), _init_l_tst1___closed__57);
v___x_291_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__56), core::ptr::addr_of_mut!(l_tst1___closed__56_once), _init_l_tst1___closed__56);
v___x_292_ = lean_nat_dec_eq(v___x_291_, v___x_290_);
return v___x_292_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__59() -> usize{
let mut v___x_293_: f64 = 0.0; let mut v___x_294_: usize = 0; 
v___x_293_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__33), core::ptr::addr_of_mut!(l_tst1___closed__33_once), _init_l_tst1___closed__33);
v___x_294_ = lean_float_to_usize(v___x_293_);
return v___x_294_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__60() -> *mut lean_object{
let mut v___x_295_: usize = 0; let mut v___x_296_: *mut lean_object = core::ptr::null_mut(); 
v___x_295_ = lean_usize_once(core::ptr::addr_of_mut!(l_tst1___closed__59), core::ptr::addr_of_mut!(l_tst1___closed__59_once), _init_l_tst1___closed__59);
v___x_296_ = lean_usize_to_nat(v___x_295_);
return v___x_296_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__61() -> u8{
let mut v___x_297_: *mut lean_object = core::ptr::null_mut(); let mut v___x_298_: *mut lean_object = core::ptr::null_mut(); let mut v___x_299_: u8 = 0; 
v___x_297_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__57), core::ptr::addr_of_mut!(l_tst1___closed__57_once), _init_l_tst1___closed__57);
v___x_298_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__60), core::ptr::addr_of_mut!(l_tst1___closed__60_once), _init_l_tst1___closed__60);
v___x_299_ = lean_nat_dec_eq(v___x_298_, v___x_297_);
return v___x_299_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__62() -> f64{
let mut v___x_300_: *mut lean_object = core::ptr::null_mut(); let mut v___x_301_: u8 = 0; let mut v___x_302_: *mut lean_object = core::ptr::null_mut(); let mut v___x_303_: f64 = 0.0; 
v___x_300_ = lean_unsigned_to_nat(1);
v___x_301_ = 1;
v___x_302_ = lean_unsigned_to_nat(14);
v___x_303_ = l_Float_ofScientific(v___x_302_, v___x_301_, v___x_300_);
return v___x_303_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__63() -> u8{
let mut v___x_304_: f64 = 0.0; let mut v___x_305_: u8 = 0; 
v___x_304_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__62), core::ptr::addr_of_mut!(l_tst1___closed__62_once), _init_l_tst1___closed__62);
v___x_305_ = lean_float_isnan(v___x_304_);
return v___x_305_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__64() -> u8{
let mut v___x_306_: f64 = 0.0; let mut v___x_307_: u8 = 0; 
v___x_306_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__62), core::ptr::addr_of_mut!(l_tst1___closed__62_once), _init_l_tst1___closed__62);
v___x_307_ = lean_float_isinf(v___x_306_);
return v___x_307_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__65() -> u8{
let mut v___x_308_: f64 = 0.0; let mut v___x_309_: u8 = 0; 
v___x_308_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__62), core::ptr::addr_of_mut!(l_tst1___closed__62_once), _init_l_tst1___closed__62);
v___x_309_ = lean_float_isfinite(v___x_308_);
return v___x_309_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__66() -> *mut lean_object{
let mut v___x_310_: f64 = 0.0; let mut v___x_311_: *mut lean_object = core::ptr::null_mut(); 
v___x_310_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__62), core::ptr::addr_of_mut!(l_tst1___closed__62_once), _init_l_tst1___closed__62);
v___x_311_ = lean_float_frexp(v___x_310_);
return v___x_311_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__67() -> *mut lean_object{
let mut v___x_312_: *mut lean_object = core::ptr::null_mut(); let mut v___x_313_: u8 = 0; let mut v___x_314_: *mut lean_object = core::ptr::null_mut(); let mut v___x_315_: *mut lean_object = core::ptr::null_mut(); 
v___x_312_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__66), core::ptr::addr_of_mut!(l_tst1___closed__66_once), _init_l_tst1___closed__66);
v___x_313_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__65), core::ptr::addr_of_mut!(l_tst1___closed__65_once), _init_l_tst1___closed__65);
v___x_314_ = lean_box((v___x_313_) as usize);
v___x_315_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_312_);
return v___x_315_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__68() -> *mut lean_object{
let mut v___x_316_: *mut lean_object = core::ptr::null_mut(); let mut v___x_317_: u8 = 0; let mut v___x_318_: *mut lean_object = core::ptr::null_mut(); let mut v___x_319_: *mut lean_object = core::ptr::null_mut(); 
v___x_316_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__67), core::ptr::addr_of_mut!(l_tst1___closed__67_once), _init_l_tst1___closed__67);
v___x_317_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__64), core::ptr::addr_of_mut!(l_tst1___closed__64_once), _init_l_tst1___closed__64);
v___x_318_ = lean_box((v___x_317_) as usize);
v___x_319_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_316_);
return v___x_319_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__69() -> *mut lean_object{
let mut v___x_320_: *mut lean_object = core::ptr::null_mut(); let mut v___x_321_: u8 = 0; let mut v___x_322_: *mut lean_object = core::ptr::null_mut(); let mut v___x_323_: *mut lean_object = core::ptr::null_mut(); 
v___x_320_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__68), core::ptr::addr_of_mut!(l_tst1___closed__68_once), _init_l_tst1___closed__68);
v___x_321_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__63), core::ptr::addr_of_mut!(l_tst1___closed__63_once), _init_l_tst1___closed__63);
v___x_322_ = lean_box((v___x_321_) as usize);
v___x_323_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_320_);
return v___x_323_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__70___boxed__const__1() -> *mut lean_object{
let mut v___x_324_: f64 = 0.0; let mut v___x_325_: *mut lean_object = core::ptr::null_mut(); 
v___x_324_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__62), core::ptr::addr_of_mut!(l_tst1___closed__62_once), _init_l_tst1___closed__62);
v___x_325_ = lean_box_float(v___x_324_);
return v___x_325_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__70() -> *mut lean_object{
let mut v___x_326_: *mut lean_object = core::ptr::null_mut(); let mut v___x_327_: *mut lean_object = core::ptr::null_mut(); let mut v___x_328_: *mut lean_object = core::ptr::null_mut(); 
v___x_326_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__69), core::ptr::addr_of_mut!(l_tst1___closed__69_once), _init_l_tst1___closed__69);
v___x_327_ = l_tst1___closed__70___boxed__const__1;
v___x_328_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_326_);
return v___x_328_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__71() -> u8{
let mut v___x_329_: f64 = 0.0; let mut v___x_330_: u8 = 0; 
v___x_329_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__23), core::ptr::addr_of_mut!(l_tst1___closed__23_once), _init_l_tst1___closed__23);
v___x_330_ = lean_float_isnan(v___x_329_);
return v___x_330_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__72() -> u8{
let mut v___x_331_: f64 = 0.0; let mut v___x_332_: u8 = 0; 
v___x_331_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__23), core::ptr::addr_of_mut!(l_tst1___closed__23_once), _init_l_tst1___closed__23);
v___x_332_ = lean_float_isinf(v___x_331_);
return v___x_332_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__73() -> u8{
let mut v___x_333_: f64 = 0.0; let mut v___x_334_: u8 = 0; 
v___x_333_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__23), core::ptr::addr_of_mut!(l_tst1___closed__23_once), _init_l_tst1___closed__23);
v___x_334_ = lean_float_isfinite(v___x_333_);
return v___x_334_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__74() -> *mut lean_object{
let mut v___x_335_: f64 = 0.0; let mut v___x_336_: *mut lean_object = core::ptr::null_mut(); 
v___x_335_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__23), core::ptr::addr_of_mut!(l_tst1___closed__23_once), _init_l_tst1___closed__23);
v___x_336_ = lean_float_frexp(v___x_335_);
return v___x_336_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__75() -> *mut lean_object{
let mut v___x_337_: *mut lean_object = core::ptr::null_mut(); let mut v___x_338_: u8 = 0; let mut v___x_339_: *mut lean_object = core::ptr::null_mut(); let mut v___x_340_: *mut lean_object = core::ptr::null_mut(); 
v___x_337_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__74), core::ptr::addr_of_mut!(l_tst1___closed__74_once), _init_l_tst1___closed__74);
v___x_338_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__73), core::ptr::addr_of_mut!(l_tst1___closed__73_once), _init_l_tst1___closed__73);
v___x_339_ = lean_box((v___x_338_) as usize);
v___x_340_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_337_);
return v___x_340_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__76() -> *mut lean_object{
let mut v___x_341_: *mut lean_object = core::ptr::null_mut(); let mut v___x_342_: u8 = 0; let mut v___x_343_: *mut lean_object = core::ptr::null_mut(); let mut v___x_344_: *mut lean_object = core::ptr::null_mut(); 
v___x_341_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__75), core::ptr::addr_of_mut!(l_tst1___closed__75_once), _init_l_tst1___closed__75);
v___x_342_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__72), core::ptr::addr_of_mut!(l_tst1___closed__72_once), _init_l_tst1___closed__72);
v___x_343_ = lean_box((v___x_342_) as usize);
v___x_344_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v___x_341_);
return v___x_344_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__77() -> *mut lean_object{
let mut v___x_345_: *mut lean_object = core::ptr::null_mut(); let mut v___x_346_: u8 = 0; let mut v___x_347_: *mut lean_object = core::ptr::null_mut(); let mut v___x_348_: *mut lean_object = core::ptr::null_mut(); 
v___x_345_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__76), core::ptr::addr_of_mut!(l_tst1___closed__76_once), _init_l_tst1___closed__76);
v___x_346_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__71), core::ptr::addr_of_mut!(l_tst1___closed__71_once), _init_l_tst1___closed__71);
v___x_347_ = lean_box((v___x_346_) as usize);
v___x_348_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_345_);
return v___x_348_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__78___boxed__const__1() -> *mut lean_object{
let mut v___x_349_: f64 = 0.0; let mut v___x_350_: *mut lean_object = core::ptr::null_mut(); 
v___x_349_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__23), core::ptr::addr_of_mut!(l_tst1___closed__23_once), _init_l_tst1___closed__23);
v___x_350_ = lean_box_float(v___x_349_);
return v___x_350_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__78() -> *mut lean_object{
let mut v___x_351_: *mut lean_object = core::ptr::null_mut(); let mut v___x_352_: *mut lean_object = core::ptr::null_mut(); let mut v___x_353_: *mut lean_object = core::ptr::null_mut(); 
v___x_351_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__77), core::ptr::addr_of_mut!(l_tst1___closed__77_once), _init_l_tst1___closed__77);
v___x_352_ = l_tst1___closed__78___boxed__const__1;
v___x_353_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
return v___x_353_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__79() -> f64{
let mut v___x_354_: f64 = 0.0; let mut v___x_355_: f64 = 0.0; 
v___x_354_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__22), core::ptr::addr_of_mut!(l_tst1___closed__22_once), _init_l_tst1___closed__22);
v___x_355_ = lean_float_negate(v___x_354_);
return v___x_355_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__80() -> f64{
let mut v___x_356_: f64 = 0.0; let mut v___x_357_: f64 = 0.0; let mut v___x_358_: f64 = 0.0; 
v___x_356_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__22), core::ptr::addr_of_mut!(l_tst1___closed__22_once), _init_l_tst1___closed__22);
v___x_357_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__79), core::ptr::addr_of_mut!(l_tst1___closed__79_once), _init_l_tst1___closed__79);
v___x_358_ = lean_float_div(v___x_357_, v___x_356_);
return v___x_358_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__81() -> u8{
let mut v___x_359_: f64 = 0.0; let mut v___x_360_: u8 = 0; 
v___x_359_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__80), core::ptr::addr_of_mut!(l_tst1___closed__80_once), _init_l_tst1___closed__80);
v___x_360_ = lean_float_isnan(v___x_359_);
return v___x_360_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__82() -> u8{
let mut v___x_361_: f64 = 0.0; let mut v___x_362_: u8 = 0; 
v___x_361_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__80), core::ptr::addr_of_mut!(l_tst1___closed__80_once), _init_l_tst1___closed__80);
v___x_362_ = lean_float_isinf(v___x_361_);
return v___x_362_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__83() -> u8{
let mut v___x_363_: f64 = 0.0; let mut v___x_364_: u8 = 0; 
v___x_363_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__80), core::ptr::addr_of_mut!(l_tst1___closed__80_once), _init_l_tst1___closed__80);
v___x_364_ = lean_float_isfinite(v___x_363_);
return v___x_364_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__84() -> *mut lean_object{
let mut v___x_365_: f64 = 0.0; let mut v___x_366_: *mut lean_object = core::ptr::null_mut(); 
v___x_365_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__80), core::ptr::addr_of_mut!(l_tst1___closed__80_once), _init_l_tst1___closed__80);
v___x_366_ = lean_float_frexp(v___x_365_);
return v___x_366_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__85() -> *mut lean_object{
let mut v___x_367_: *mut lean_object = core::ptr::null_mut(); let mut v___x_368_: u8 = 0; let mut v___x_369_: *mut lean_object = core::ptr::null_mut(); let mut v___x_370_: *mut lean_object = core::ptr::null_mut(); 
v___x_367_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__84), core::ptr::addr_of_mut!(l_tst1___closed__84_once), _init_l_tst1___closed__84);
v___x_368_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__83), core::ptr::addr_of_mut!(l_tst1___closed__83_once), _init_l_tst1___closed__83);
v___x_369_ = lean_box((v___x_368_) as usize);
v___x_370_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v___x_367_);
return v___x_370_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__86() -> *mut lean_object{
let mut v___x_371_: *mut lean_object = core::ptr::null_mut(); let mut v___x_372_: u8 = 0; let mut v___x_373_: *mut lean_object = core::ptr::null_mut(); let mut v___x_374_: *mut lean_object = core::ptr::null_mut(); 
v___x_371_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__85), core::ptr::addr_of_mut!(l_tst1___closed__85_once), _init_l_tst1___closed__85);
v___x_372_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__82), core::ptr::addr_of_mut!(l_tst1___closed__82_once), _init_l_tst1___closed__82);
v___x_373_ = lean_box((v___x_372_) as usize);
v___x_374_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___x_371_);
return v___x_374_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__87() -> *mut lean_object{
let mut v___x_375_: *mut lean_object = core::ptr::null_mut(); let mut v___x_376_: u8 = 0; let mut v___x_377_: *mut lean_object = core::ptr::null_mut(); let mut v___x_378_: *mut lean_object = core::ptr::null_mut(); 
v___x_375_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__86), core::ptr::addr_of_mut!(l_tst1___closed__86_once), _init_l_tst1___closed__86);
v___x_376_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__81), core::ptr::addr_of_mut!(l_tst1___closed__81_once), _init_l_tst1___closed__81);
v___x_377_ = lean_box((v___x_376_) as usize);
v___x_378_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v___x_375_);
return v___x_378_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__88___boxed__const__1() -> *mut lean_object{
let mut v___x_379_: f64 = 0.0; let mut v___x_380_: *mut lean_object = core::ptr::null_mut(); 
v___x_379_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__80), core::ptr::addr_of_mut!(l_tst1___closed__80_once), _init_l_tst1___closed__80);
v___x_380_ = lean_box_float(v___x_379_);
return v___x_380_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__88() -> *mut lean_object{
let mut v___x_381_: *mut lean_object = core::ptr::null_mut(); let mut v___x_382_: *mut lean_object = core::ptr::null_mut(); let mut v___x_383_: *mut lean_object = core::ptr::null_mut(); 
v___x_381_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__87), core::ptr::addr_of_mut!(l_tst1___closed__87_once), _init_l_tst1___closed__87);
v___x_382_ = l_tst1___closed__88___boxed__const__1;
v___x_383_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
return v___x_383_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__89() -> u8{
let mut v___x_384_: f64 = 0.0; let mut v___x_385_: u8 = 0; 
v___x_384_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__33), core::ptr::addr_of_mut!(l_tst1___closed__33_once), _init_l_tst1___closed__33);
v___x_385_ = lean_float_isnan(v___x_384_);
return v___x_385_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__90() -> u8{
let mut v___x_386_: f64 = 0.0; let mut v___x_387_: u8 = 0; 
v___x_386_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__33), core::ptr::addr_of_mut!(l_tst1___closed__33_once), _init_l_tst1___closed__33);
v___x_387_ = lean_float_isinf(v___x_386_);
return v___x_387_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__91() -> u8{
let mut v___x_388_: f64 = 0.0; let mut v___x_389_: u8 = 0; 
v___x_388_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__33), core::ptr::addr_of_mut!(l_tst1___closed__33_once), _init_l_tst1___closed__33);
v___x_389_ = lean_float_isfinite(v___x_388_);
return v___x_389_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__92() -> *mut lean_object{
let mut v___x_390_: f64 = 0.0; let mut v___x_391_: *mut lean_object = core::ptr::null_mut(); 
v___x_390_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__33), core::ptr::addr_of_mut!(l_tst1___closed__33_once), _init_l_tst1___closed__33);
v___x_391_ = lean_float_frexp(v___x_390_);
return v___x_391_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__93() -> *mut lean_object{
let mut v___x_392_: *mut lean_object = core::ptr::null_mut(); let mut v___x_393_: u8 = 0; let mut v___x_394_: *mut lean_object = core::ptr::null_mut(); let mut v___x_395_: *mut lean_object = core::ptr::null_mut(); 
v___x_392_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__92), core::ptr::addr_of_mut!(l_tst1___closed__92_once), _init_l_tst1___closed__92);
v___x_393_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__91), core::ptr::addr_of_mut!(l_tst1___closed__91_once), _init_l_tst1___closed__91);
v___x_394_ = lean_box((v___x_393_) as usize);
v___x_395_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_392_);
return v___x_395_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__94() -> *mut lean_object{
let mut v___x_396_: *mut lean_object = core::ptr::null_mut(); let mut v___x_397_: u8 = 0; let mut v___x_398_: *mut lean_object = core::ptr::null_mut(); let mut v___x_399_: *mut lean_object = core::ptr::null_mut(); 
v___x_396_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__93), core::ptr::addr_of_mut!(l_tst1___closed__93_once), _init_l_tst1___closed__93);
v___x_397_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__90), core::ptr::addr_of_mut!(l_tst1___closed__90_once), _init_l_tst1___closed__90);
v___x_398_ = lean_box((v___x_397_) as usize);
v___x_399_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___x_396_);
return v___x_399_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__95() -> *mut lean_object{
let mut v___x_400_: *mut lean_object = core::ptr::null_mut(); let mut v___x_401_: u8 = 0; let mut v___x_402_: *mut lean_object = core::ptr::null_mut(); let mut v___x_403_: *mut lean_object = core::ptr::null_mut(); 
v___x_400_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__94), core::ptr::addr_of_mut!(l_tst1___closed__94_once), _init_l_tst1___closed__94);
v___x_401_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__89), core::ptr::addr_of_mut!(l_tst1___closed__89_once), _init_l_tst1___closed__89);
v___x_402_ = lean_box((v___x_401_) as usize);
v___x_403_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_400_);
return v___x_403_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__96___boxed__const__1() -> *mut lean_object{
let mut v___x_404_: f64 = 0.0; let mut v___x_405_: *mut lean_object = core::ptr::null_mut(); 
v___x_404_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__33), core::ptr::addr_of_mut!(l_tst1___closed__33_once), _init_l_tst1___closed__33);
v___x_405_ = lean_box_float(v___x_404_);
return v___x_405_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__96() -> *mut lean_object{
let mut v___x_406_: *mut lean_object = core::ptr::null_mut(); let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); let mut v___x_408_: *mut lean_object = core::ptr::null_mut(); 
v___x_406_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__95), core::ptr::addr_of_mut!(l_tst1___closed__95_once), _init_l_tst1___closed__95);
v___x_407_ = l_tst1___closed__96___boxed__const__1;
v___x_408_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_406_);
return v___x_408_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__97() -> f64{
let mut v___x_409_: f64 = 0.0; let mut v___x_410_: f64 = 0.0; let mut v___x_411_: f64 = 0.0; 
v___x_409_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__22), core::ptr::addr_of_mut!(l_tst1___closed__22_once), _init_l_tst1___closed__22);
v___x_410_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__29), core::ptr::addr_of_mut!(l_tst1___closed__29_once), _init_l_tst1___closed__29);
v___x_411_ = lean_float_div(v___x_410_, v___x_409_);
return v___x_411_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__98() -> u8{
let mut v___x_412_: f64 = 0.0; let mut v___x_413_: u8 = 0; 
v___x_412_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__97), core::ptr::addr_of_mut!(l_tst1___closed__97_once), _init_l_tst1___closed__97);
v___x_413_ = lean_float_isnan(v___x_412_);
return v___x_413_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__99() -> u8{
let mut v___x_414_: f64 = 0.0; let mut v___x_415_: u8 = 0; 
v___x_414_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__97), core::ptr::addr_of_mut!(l_tst1___closed__97_once), _init_l_tst1___closed__97);
v___x_415_ = lean_float_isinf(v___x_414_);
return v___x_415_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__100() -> u8{
let mut v___x_416_: f64 = 0.0; let mut v___x_417_: u8 = 0; 
v___x_416_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__97), core::ptr::addr_of_mut!(l_tst1___closed__97_once), _init_l_tst1___closed__97);
v___x_417_ = lean_float_isfinite(v___x_416_);
return v___x_417_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__101() -> *mut lean_object{
let mut v___x_418_: f64 = 0.0; let mut v___x_419_: *mut lean_object = core::ptr::null_mut(); 
v___x_418_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__97), core::ptr::addr_of_mut!(l_tst1___closed__97_once), _init_l_tst1___closed__97);
v___x_419_ = lean_float_frexp(v___x_418_);
return v___x_419_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__102() -> *mut lean_object{
let mut v___x_420_: *mut lean_object = core::ptr::null_mut(); let mut v___x_421_: u8 = 0; let mut v___x_422_: *mut lean_object = core::ptr::null_mut(); let mut v___x_423_: *mut lean_object = core::ptr::null_mut(); 
v___x_420_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__101), core::ptr::addr_of_mut!(l_tst1___closed__101_once), _init_l_tst1___closed__101);
v___x_421_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__100), core::ptr::addr_of_mut!(l_tst1___closed__100_once), _init_l_tst1___closed__100);
v___x_422_ = lean_box((v___x_421_) as usize);
v___x_423_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_420_);
return v___x_423_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__103() -> *mut lean_object{
let mut v___x_424_: *mut lean_object = core::ptr::null_mut(); let mut v___x_425_: u8 = 0; let mut v___x_426_: *mut lean_object = core::ptr::null_mut(); let mut v___x_427_: *mut lean_object = core::ptr::null_mut(); 
v___x_424_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__102), core::ptr::addr_of_mut!(l_tst1___closed__102_once), _init_l_tst1___closed__102);
v___x_425_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__99), core::ptr::addr_of_mut!(l_tst1___closed__99_once), _init_l_tst1___closed__99);
v___x_426_ = lean_box((v___x_425_) as usize);
v___x_427_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v___x_424_);
return v___x_427_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__104() -> *mut lean_object{
let mut v___x_428_: *mut lean_object = core::ptr::null_mut(); let mut v___x_429_: u8 = 0; let mut v___x_430_: *mut lean_object = core::ptr::null_mut(); let mut v___x_431_: *mut lean_object = core::ptr::null_mut(); 
v___x_428_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__103), core::ptr::addr_of_mut!(l_tst1___closed__103_once), _init_l_tst1___closed__103);
v___x_429_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__98), core::ptr::addr_of_mut!(l_tst1___closed__98_once), _init_l_tst1___closed__98);
v___x_430_ = lean_box((v___x_429_) as usize);
v___x_431_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___x_428_);
return v___x_431_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__105___boxed__const__1() -> *mut lean_object{
let mut v___x_432_: f64 = 0.0; let mut v___x_433_: *mut lean_object = core::ptr::null_mut(); 
v___x_432_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__97), core::ptr::addr_of_mut!(l_tst1___closed__97_once), _init_l_tst1___closed__97);
v___x_433_ = lean_box_float(v___x_432_);
return v___x_433_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__105() -> *mut lean_object{
let mut v___x_434_: *mut lean_object = core::ptr::null_mut(); let mut v___x_435_: *mut lean_object = core::ptr::null_mut(); let mut v___x_436_: *mut lean_object = core::ptr::null_mut(); 
v___x_434_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__104), core::ptr::addr_of_mut!(l_tst1___closed__104_once), _init_l_tst1___closed__104);
v___x_435_ = l_tst1___closed__105___boxed__const__1;
v___x_436_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v___x_434_);
return v___x_436_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__106() -> f64{
let mut v___x_437_: f64 = 0.0; let mut v___x_438_: f64 = 0.0; let mut v___x_439_: f64 = 0.0; 
v___x_437_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__29), core::ptr::addr_of_mut!(l_tst1___closed__29_once), _init_l_tst1___closed__29);
v___x_438_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__1), core::ptr::addr_of_mut!(l_tst1___closed__1_once), _init_l_tst1___closed__1);
v___x_439_ = pow(v___x_438_, v___x_437_);
return v___x_439_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__107() -> f64{
let mut v___x_440_: *mut lean_object = core::ptr::null_mut(); let mut v___x_441_: u8 = 0; let mut v___x_442_: *mut lean_object = core::ptr::null_mut(); let mut v___x_443_: f64 = 0.0; 
v___x_440_ = lean_unsigned_to_nat(1);
v___x_441_ = 1;
v___x_442_ = lean_unsigned_to_nat(22);
v___x_443_ = l_Float_ofScientific(v___x_442_, v___x_441_, v___x_440_);
return v___x_443_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_tst1___closed__108() -> f64{
let mut v___x_444_: f64 = 0.0; let mut v___x_445_: f64 = 0.0; 
v___x_444_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__107), core::ptr::addr_of_mut!(l_tst1___closed__107_once), _init_l_tst1___closed__107);
v___x_445_ = pow(v___x_444_, v___x_444_);
return v___x_445_;
}
#[no_mangle] pub unsafe extern "C" fn l_tst1() -> *mut lean_object{
let mut v___x_447_: f64 = 0.0; let mut v___x_448_: *mut lean_object = core::ptr::null_mut(); 
v___x_447_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__0), core::ptr::addr_of_mut!(l_tst1___closed__0_once), _init_l_tst1___closed__0);
v___x_448_ = l_IO_println___at___00tst1_spec__0(v___x_447_);
if lean_obj_tag(v___x_448_) == 0 {
let mut v___x_449_: f64 = 0.0; let mut v___x_450_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_448_, 1);
v___x_449_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__2), core::ptr::addr_of_mut!(l_tst1___closed__2_once), _init_l_tst1___closed__2);
v___x_450_ = l_IO_println___at___00tst1_spec__0(v___x_449_);
if lean_obj_tag(v___x_450_) == 0 {
let mut v___x_451_: f64 = 0.0; let mut v___x_452_: u8 = 0; let mut v___x_453_: u8 = 0; let mut v___x_454_: u8 = 0; let mut v___x_455_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_450_, 1);
v___x_451_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__4), core::ptr::addr_of_mut!(l_tst1___closed__4_once), _init_l_tst1___closed__4);
v___x_452_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__5), core::ptr::addr_of_mut!(l_tst1___closed__5_once), _init_l_tst1___closed__5);
v___x_453_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__6), core::ptr::addr_of_mut!(l_tst1___closed__6_once), _init_l_tst1___closed__6);
v___x_454_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__7), core::ptr::addr_of_mut!(l_tst1___closed__7_once), _init_l_tst1___closed__7);
v___x_455_ = l_IO_println___at___00tst1_spec__0(v___x_451_);
if lean_obj_tag(v___x_455_) == 0 {
let mut v___x_456_: f64 = 0.0; let mut v___x_457_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_455_, 1);
v___x_456_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__8), core::ptr::addr_of_mut!(l_tst1___closed__8_once), _init_l_tst1___closed__8);
v___x_457_ = l_IO_println___at___00tst1_spec__0(v___x_456_);
if lean_obj_tag(v___x_457_) == 0 {
let mut v___x_458_: f64 = 0.0; let mut v___x_459_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_457_, 1);
v___x_458_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__9), core::ptr::addr_of_mut!(l_tst1___closed__9_once), _init_l_tst1___closed__9);
v___x_459_ = l_IO_println___at___00tst1_spec__0(v___x_458_);
if lean_obj_tag(v___x_459_) == 0 {
let mut v___x_460_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_459_, 1);
v___x_460_ = l_IO_println___at___00tst1_spec__1(v___x_452_);
if lean_obj_tag(v___x_460_) == 0 {
let mut v___x_461_: u8 = 0; let mut v___x_462_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_460_, 1);
v___x_461_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__11), core::ptr::addr_of_mut!(l_tst1___closed__11_once), _init_l_tst1___closed__11);
v___x_462_ = l_IO_println___at___00tst1_spec__1(v___x_461_);
if lean_obj_tag(v___x_462_) == 0 {
let mut v___x_463_: u8 = 0; let mut v___x_464_: u8 = 0; let mut v___x_465_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_462_, 1);
v___x_463_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__12), core::ptr::addr_of_mut!(l_tst1___closed__12_once), _init_l_tst1___closed__12);
v___x_464_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__13), core::ptr::addr_of_mut!(l_tst1___closed__13_once), _init_l_tst1___closed__13);
v___x_465_ = l_IO_println___at___00tst1_spec__1(v___x_464_);
if lean_obj_tag(v___x_465_) == 0 {
let mut v___x_466_: u8 = 0; let mut v___x_467_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_465_, 1);
v___x_466_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__14), core::ptr::addr_of_mut!(l_tst1___closed__14_once), _init_l_tst1___closed__14);
v___x_467_ = l_IO_println___at___00tst1_spec__1(v___x_466_);
if lean_obj_tag(v___x_467_) == 0 {
let mut v___x_468_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_467_, 1);
v___x_468_ = l_IO_println___at___00tst1_spec__1(v___x_453_);
if lean_obj_tag(v___x_468_) == 0 {
let mut v___x_469_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_468_, 1);
v___x_469_ = l_IO_println___at___00tst1_spec__1(v___x_454_);
if lean_obj_tag(v___x_469_) == 0 {
let mut v___x_470_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_469_, 1);
v___x_470_ = l_IO_println___at___00tst1_spec__1(v___x_463_);
if lean_obj_tag(v___x_470_) == 0 {
let mut v___x_471_: f64 = 0.0; let mut v___x_472_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_470_, 1);
v___x_471_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__16), core::ptr::addr_of_mut!(l_tst1___closed__16_once), _init_l_tst1___closed__16);
v___x_472_ = l_IO_println___at___00tst1_spec__0(v___x_471_);
if lean_obj_tag(v___x_472_) == 0 {
let mut v___x_473_: f64 = 0.0; let mut v___x_474_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_472_, 1);
v___x_473_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__18), core::ptr::addr_of_mut!(l_tst1___closed__18_once), _init_l_tst1___closed__18);
v___x_474_ = l_IO_println___at___00tst1_spec__0(v___x_473_);
if lean_obj_tag(v___x_474_) == 0 {
let mut v___x_475_: f64 = 0.0; let mut v___x_476_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_474_, 1);
v___x_475_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__20), core::ptr::addr_of_mut!(l_tst1___closed__20_once), _init_l_tst1___closed__20);
v___x_476_ = l_IO_println___at___00tst1_spec__0(v___x_475_);
if lean_obj_tag(v___x_476_) == 0 {
let mut v___x_477_: f64 = 0.0; let mut v___x_478_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_476_, 1);
v___x_477_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__21), core::ptr::addr_of_mut!(l_tst1___closed__21_once), _init_l_tst1___closed__21);
v___x_478_ = l_IO_println___at___00tst1_spec__0(v___x_477_);
if lean_obj_tag(v___x_478_) == 0 {
let mut v___x_479_: u8 = 0; let mut v___x_480_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_478_, 1);
v___x_479_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__24), core::ptr::addr_of_mut!(l_tst1___closed__24_once), _init_l_tst1___closed__24);
v___x_480_ = l_IO_println___at___00tst1_spec__2(v___x_479_);
if lean_obj_tag(v___x_480_) == 0 {
let mut v___x_481_: u16 = 0; let mut v___x_482_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_480_, 1);
v___x_481_ = lean_uint16_once(core::ptr::addr_of_mut!(l_tst1___closed__25), core::ptr::addr_of_mut!(l_tst1___closed__25_once), _init_l_tst1___closed__25);
v___x_482_ = l_IO_println___at___00tst1_spec__3(v___x_481_);
if lean_obj_tag(v___x_482_) == 0 {
let mut v___x_483_: u32 = 0; let mut v___x_484_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_482_, 1);
v___x_483_ = lean_uint32_once(core::ptr::addr_of_mut!(l_tst1___closed__26), core::ptr::addr_of_mut!(l_tst1___closed__26_once), _init_l_tst1___closed__26);
v___x_484_ = l_IO_println___at___00tst1_spec__4(v___x_483_);
if lean_obj_tag(v___x_484_) == 0 {
let mut v___x_485_: u64 = 0; let mut v___x_486_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_484_, 1);
v___x_485_ = lean_uint64_once(core::ptr::addr_of_mut!(l_tst1___closed__27), core::ptr::addr_of_mut!(l_tst1___closed__27_once), _init_l_tst1___closed__27);
v___x_486_ = l_IO_println___at___00tst1_spec__5(v___x_485_);
if lean_obj_tag(v___x_486_) == 0 {
let mut v___x_487_: usize = 0; let mut v___x_488_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_486_, 1);
v___x_487_ = lean_usize_once(core::ptr::addr_of_mut!(l_tst1___closed__28), core::ptr::addr_of_mut!(l_tst1___closed__28_once), _init_l_tst1___closed__28);
v___x_488_ = l_IO_println___at___00tst1_spec__6(v___x_487_);
if lean_obj_tag(v___x_488_) == 0 {
let mut v___x_489_: u8 = 0; let mut v___x_490_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_488_, 1);
v___x_489_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__30), core::ptr::addr_of_mut!(l_tst1___closed__30_once), _init_l_tst1___closed__30);
v___x_490_ = l_IO_println___at___00tst1_spec__2(v___x_489_);
if lean_obj_tag(v___x_490_) == 0 {
let mut v___x_491_: u8 = 0; let mut v___x_492_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_490_, 1);
v___x_491_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__32), core::ptr::addr_of_mut!(l_tst1___closed__32_once), _init_l_tst1___closed__32);
v___x_492_ = l_IO_println___at___00tst1_spec__2(v___x_491_);
if lean_obj_tag(v___x_492_) == 0 {
let mut v___x_493_: u8 = 0; let mut v___x_494_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_492_, 1);
v___x_493_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__34), core::ptr::addr_of_mut!(l_tst1___closed__34_once), _init_l_tst1___closed__34);
v___x_494_ = l_IO_println___at___00tst1_spec__2(v___x_493_);
if lean_obj_tag(v___x_494_) == 0 {
let mut v___x_495_: u16 = 0; let mut v___x_496_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_494_, 1);
v___x_495_ = lean_uint16_once(core::ptr::addr_of_mut!(l_tst1___closed__35), core::ptr::addr_of_mut!(l_tst1___closed__35_once), _init_l_tst1___closed__35);
v___x_496_ = l_IO_println___at___00tst1_spec__3(v___x_495_);
if lean_obj_tag(v___x_496_) == 0 {
let mut v___x_497_: u16 = 0; let mut v___x_498_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_496_, 1);
v___x_497_ = lean_uint16_once(core::ptr::addr_of_mut!(l_tst1___closed__38), core::ptr::addr_of_mut!(l_tst1___closed__38_once), _init_l_tst1___closed__38);
v___x_498_ = l_IO_println___at___00tst1_spec__3(v___x_497_);
if lean_obj_tag(v___x_498_) == 0 {
let mut v___x_499_: u16 = 0; let mut v___x_500_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_498_, 1);
v___x_499_ = lean_uint16_once(core::ptr::addr_of_mut!(l_tst1___closed__39), core::ptr::addr_of_mut!(l_tst1___closed__39_once), _init_l_tst1___closed__39);
v___x_500_ = l_IO_println___at___00tst1_spec__3(v___x_499_);
if lean_obj_tag(v___x_500_) == 0 {
let mut v___x_501_: u32 = 0; let mut v___x_502_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_500_, 1);
v___x_501_ = lean_uint32_once(core::ptr::addr_of_mut!(l_tst1___closed__40), core::ptr::addr_of_mut!(l_tst1___closed__40_once), _init_l_tst1___closed__40);
v___x_502_ = l_IO_println___at___00tst1_spec__4(v___x_501_);
if lean_obj_tag(v___x_502_) == 0 {
let mut v___x_503_: u32 = 0; let mut v___x_504_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_502_, 1);
v___x_503_ = lean_uint32_once(core::ptr::addr_of_mut!(l_tst1___closed__43), core::ptr::addr_of_mut!(l_tst1___closed__43_once), _init_l_tst1___closed__43);
v___x_504_ = l_IO_println___at___00tst1_spec__4(v___x_503_);
if lean_obj_tag(v___x_504_) == 0 {
let mut v___x_505_: u32 = 0; let mut v___x_506_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_504_, 1);
v___x_505_ = lean_uint32_once(core::ptr::addr_of_mut!(l_tst1___closed__44), core::ptr::addr_of_mut!(l_tst1___closed__44_once), _init_l_tst1___closed__44);
v___x_506_ = l_IO_println___at___00tst1_spec__4(v___x_505_);
if lean_obj_tag(v___x_506_) == 0 {
let mut v___x_507_: u64 = 0; let mut v___x_508_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_506_, 1);
v___x_507_ = lean_uint64_once(core::ptr::addr_of_mut!(l_tst1___closed__45), core::ptr::addr_of_mut!(l_tst1___closed__45_once), _init_l_tst1___closed__45);
v___x_508_ = l_IO_println___at___00tst1_spec__5(v___x_507_);
if lean_obj_tag(v___x_508_) == 0 {
let mut v___x_509_: u64 = 0; let mut v___x_510_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_508_, 1);
v___x_509_ = lean_uint64_once(core::ptr::addr_of_mut!(l_tst1___closed__48), core::ptr::addr_of_mut!(l_tst1___closed__48_once), _init_l_tst1___closed__48);
v___x_510_ = l_IO_println___at___00tst1_spec__5(v___x_509_);
if lean_obj_tag(v___x_510_) == 0 {
let mut v___x_511_: u64 = 0; let mut v___x_512_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_510_, 1);
v___x_511_ = lean_uint64_once(core::ptr::addr_of_mut!(l_tst1___closed__49), core::ptr::addr_of_mut!(l_tst1___closed__49_once), _init_l_tst1___closed__49);
v___x_512_ = l_IO_println___at___00tst1_spec__5(v___x_511_);
if lean_obj_tag(v___x_512_) == 0 {
let mut v___x_513_: usize = 0; let mut v___x_514_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_512_, 1);
v___x_513_ = lean_usize_once(core::ptr::addr_of_mut!(l_tst1___closed__50), core::ptr::addr_of_mut!(l_tst1___closed__50_once), _init_l_tst1___closed__50);
v___x_514_ = l_IO_println___at___00tst1_spec__6(v___x_513_);
if lean_obj_tag(v___x_514_) == 0 {
let mut v___x_515_: u8 = 0; let mut v___x_516_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_514_, 1);
v___x_515_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__58), core::ptr::addr_of_mut!(l_tst1___closed__58_once), _init_l_tst1___closed__58);
v___x_516_ = l_IO_println___at___00tst1_spec__1(v___x_515_);
if lean_obj_tag(v___x_516_) == 0 {
let mut v___x_517_: u8 = 0; let mut v___x_518_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_516_, 1);
v___x_517_ = lean_uint8_once(core::ptr::addr_of_mut!(l_tst1___closed__61), core::ptr::addr_of_mut!(l_tst1___closed__61_once), _init_l_tst1___closed__61);
v___x_518_ = l_IO_println___at___00tst1_spec__1(v___x_517_);
if lean_obj_tag(v___x_518_) == 0 {
let mut v___x_519_: *mut lean_object = core::ptr::null_mut(); let mut v___x_520_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_518_, 1);
v___x_519_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__70), core::ptr::addr_of_mut!(l_tst1___closed__70_once), _init_l_tst1___closed__70);
v___x_520_ = l_IO_println___at___00tst1_spec__7(v___x_519_);
if lean_obj_tag(v___x_520_) == 0 {
let mut v___x_521_: *mut lean_object = core::ptr::null_mut(); let mut v___x_522_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_520_, 1);
v___x_521_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__78), core::ptr::addr_of_mut!(l_tst1___closed__78_once), _init_l_tst1___closed__78);
v___x_522_ = l_IO_println___at___00tst1_spec__7(v___x_521_);
if lean_obj_tag(v___x_522_) == 0 {
let mut v___x_523_: *mut lean_object = core::ptr::null_mut(); let mut v___x_524_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_522_, 1);
v___x_523_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__88), core::ptr::addr_of_mut!(l_tst1___closed__88_once), _init_l_tst1___closed__88);
v___x_524_ = l_IO_println___at___00tst1_spec__7(v___x_523_);
if lean_obj_tag(v___x_524_) == 0 {
let mut v___x_525_: *mut lean_object = core::ptr::null_mut(); let mut v___x_526_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_524_, 1);
v___x_525_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__96), core::ptr::addr_of_mut!(l_tst1___closed__96_once), _init_l_tst1___closed__96);
v___x_526_ = l_IO_println___at___00tst1_spec__7(v___x_525_);
if lean_obj_tag(v___x_526_) == 0 {
let mut v___x_527_: *mut lean_object = core::ptr::null_mut(); let mut v___x_528_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_526_, 1);
v___x_527_ = lean_obj_once(core::ptr::addr_of_mut!(l_tst1___closed__105), core::ptr::addr_of_mut!(l_tst1___closed__105_once), _init_l_tst1___closed__105);
v___x_528_ = l_IO_println___at___00tst1_spec__7(v___x_527_);
if lean_obj_tag(v___x_528_) == 0 {
let mut v___x_529_: f64 = 0.0; let mut v___x_530_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_528_, 1);
v___x_529_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__106), core::ptr::addr_of_mut!(l_tst1___closed__106_once), _init_l_tst1___closed__106);
v___x_530_ = l_IO_println___at___00tst1_spec__0(v___x_529_);
if lean_obj_tag(v___x_530_) == 0 {
let mut v___x_531_: f64 = 0.0; let mut v___x_532_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_530_, 1);
v___x_531_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__108), core::ptr::addr_of_mut!(l_tst1___closed__108_once), _init_l_tst1___closed__108);
v___x_532_ = l_IO_println___at___00tst1_spec__0(v___x_531_);
return v___x_532_;
} else {
return v___x_530_;
}
} else {
return v___x_528_;
}
} else {
return v___x_526_;
}
} else {
return v___x_524_;
}
} else {
return v___x_522_;
}
} else {
return v___x_520_;
}
} else {
return v___x_518_;
}
} else {
return v___x_516_;
}
} else {
return v___x_514_;
}
} else {
return v___x_512_;
}
} else {
return v___x_510_;
}
} else {
return v___x_508_;
}
} else {
return v___x_506_;
}
} else {
return v___x_504_;
}
} else {
return v___x_502_;
}
} else {
return v___x_500_;
}
} else {
return v___x_498_;
}
} else {
return v___x_496_;
}
} else {
return v___x_494_;
}
} else {
return v___x_492_;
}
} else {
return v___x_490_;
}
} else {
return v___x_488_;
}
} else {
return v___x_486_;
}
} else {
return v___x_484_;
}
} else {
return v___x_482_;
}
} else {
return v___x_480_;
}
} else {
return v___x_478_;
}
} else {
return v___x_476_;
}
} else {
return v___x_474_;
}
} else {
return v___x_472_;
}
} else {
return v___x_470_;
}
} else {
return v___x_469_;
}
} else {
return v___x_468_;
}
} else {
return v___x_467_;
}
} else {
return v___x_465_;
}
} else {
return v___x_462_;
}
} else {
return v___x_460_;
}
} else {
return v___x_459_;
}
} else {
return v___x_457_;
}
} else {
return v___x_455_;
}
} else {
return v___x_450_;
}
} else {
return v___x_448_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_tst1___boxed(mut v_a_533_: *mut lean_object) -> *mut lean_object{
let mut v_res_534_: *mut lean_object = core::ptr::null_mut(); 
v_res_534_ = l_tst1();
return v_res_534_;
}
#[no_mangle] pub unsafe extern "C" fn l_mkFoo(mut v_x_535_: *mut lean_object) -> *mut lean_object{
let mut v___x_536_: u64 = 0; let mut v___x_537_: f64 = 0.0; let mut v___x_538_: f64 = 0.0; let mut v___x_539_: f64 = 0.0; let mut v___x_540_: f64 = 0.0; let mut v___x_541_: f64 = 0.0; let mut v___x_542_: *mut lean_object = core::ptr::null_mut(); 
v___x_536_ = lean_uint64_of_nat(v_x_535_);
lean_inc(v_x_535_);
v___x_537_ = lean_float_of_nat(v_x_535_);
v___x_538_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__3), core::ptr::addr_of_mut!(l_tst1___closed__3_once), _init_l_tst1___closed__3);
v___x_539_ = lean_float_div(v___x_537_, v___x_538_);
v___x_540_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__1), core::ptr::addr_of_mut!(l_tst1___closed__1_once), _init_l_tst1___closed__1);
v___x_541_ = lean_float_div(v___x_537_, v___x_540_);
v___x_542_ = lean_alloc_ctor(0, 1, (24) as u32);
lean_ctor_set(v___x_542_, 0, v_x_535_);
lean_ctor_set_uint64(v___x_542_, (core::mem::size_of::<*mut lean_object>()*1) as u32, v___x_536_);
lean_ctor_set_float(v___x_542_, (core::mem::size_of::<*mut lean_object>()*1 + 8) as u32, v___x_539_);
lean_ctor_set_float(v___x_542_, (core::mem::size_of::<*mut lean_object>()*1 + 16) as u32, v___x_541_);
return v___x_542_;
}
#[no_mangle] pub unsafe extern "C" fn l_tst2(mut v_x_543_: *mut lean_object) -> *mut lean_object{
let mut v_foo_545_: *mut lean_object = core::ptr::null_mut(); let mut v_y_546_: f64 = 0.0; let mut v_z_547_: f64 = 0.0; let mut v___x_548_: *mut lean_object = core::ptr::null_mut(); 
v_foo_545_ = l_mkFoo(v_x_543_);
v_y_546_ = lean_ctor_get_float(v_foo_545_, (core::mem::size_of::<*mut lean_object>()*1 + 8) as u32);
v_z_547_ = lean_ctor_get_float(v_foo_545_, (core::mem::size_of::<*mut lean_object>()*1 + 16) as u32);
lean_dec_ref(v_foo_545_);
v___x_548_ = l_IO_println___at___00tst1_spec__0(v_y_546_);
if lean_obj_tag(v___x_548_) == 0 {
let mut v___x_549_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_548_, 1);
v___x_549_ = l_IO_println___at___00tst1_spec__0(v_z_547_);
return v___x_549_;
} else {
return v___x_548_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_tst2___boxed(mut v_x_550_: *mut lean_object, mut v_a_551_: *mut lean_object) -> *mut lean_object{
let mut v_res_552_: *mut lean_object = core::ptr::null_mut(); 
v_res_552_ = l_tst2(v_x_550_);
return v_res_552_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_mapTR_loop___at___00fMap_spec__0(mut v_f_553_: *mut lean_object, mut v_a_554_: *mut lean_object, mut v_a_555_: *mut lean_object) -> *mut lean_object{
let mut v___x_556_: *mut lean_object = core::ptr::null_mut(); let mut v_head_557_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_558_: *mut lean_object = core::ptr::null_mut(); let mut v___x_560_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_561_: u8 = 0; let mut v___x_562_: *mut lean_object = core::ptr::null_mut(); let mut v___x_564_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_566_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_567_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_a_554_) == 0 {
lean_dec_ref(v_f_553_);
v___x_556_ = l_List_reverse___redArg(v_a_555_);
return v___x_556_;
} else {
v_head_557_ = lean_ctor_get(v_a_554_, 0);
v_tail_558_ = lean_ctor_get(v_a_554_, 1);
v_isSharedCheck_567_ = (!lean_is_exclusive(v_a_554_)) as u8;
if v_isSharedCheck_567_ == 0 {
v___x_560_ = v_a_554_;
v_isShared_561_ = v_isSharedCheck_567_;
state = 1; continue;
} else {
lean_inc(v_tail_558_);
lean_inc(v_head_557_);
lean_dec(v_a_554_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_567_;
state = 1; continue;
}
}
}
1 => {
lean_inc_ref(v_f_553_);
v___x_562_ = lean_apply_1(v_f_553_, v_head_557_);
if v_isShared_561_ == 0 {
lean_ctor_set(v___x_560_, 1, v_a_555_);
lean_ctor_set(v___x_560_, 0, v___x_562_);
v___x_564_ = v___x_560_;
state = 2; continue;
} else {
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_a_555_);
v___x_564_ = v_reuseFailAlloc_566_;
state = 2; continue;
}
}
2 => {
v_a_554_ = v_tail_558_;
v_a_555_ = v___x_564_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_fMap(mut v_f_568_: *mut lean_object, mut v_xs_569_: *mut lean_object) -> *mut lean_object{
let mut v___x_570_: *mut lean_object = core::ptr::null_mut(); let mut v___x_571_: *mut lean_object = core::ptr::null_mut(); 
v___x_570_ = lean_box(0);
v___x_571_ = l_List_mapTR_loop___at___00fMap_spec__0(v_f_568_, v_xs_569_, v___x_570_);
return v___x_571_;
}
#[no_mangle] pub unsafe extern "C" fn l_tst3___lam__0(mut v_y_572_: f64, mut v_x_573_: f64) -> f64{
let mut v___x_574_: f64 = 0.0; 
v___x_574_ = lean_float_div(v_x_573_, v_y_572_);
return v___x_574_;
}
#[no_mangle] pub unsafe extern "C" fn l_tst3___lam__0___boxed(mut v_y_575_: *mut lean_object, mut v_x_576_: *mut lean_object) -> *mut lean_object{
let mut v_y_boxed_577_: f64 = 0.0; let mut v_x_boxed_578_: f64 = 0.0; let mut v_res_579_: f64 = 0.0; let mut v_r_580_: *mut lean_object = core::ptr::null_mut(); 
v_y_boxed_577_ = lean_unbox_float(v_y_575_);
lean_dec_ref(v_y_575_);
v_x_boxed_578_ = lean_unbox_float(v_x_576_);
lean_dec_ref(v_x_576_);
v_res_579_ = l_tst3___lam__0(v_y_boxed_577_, v_x_boxed_578_);
v_r_580_ = lean_box_float(v_res_579_);
return v_r_580_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_foldl___at___00List_toString___at___00IO_println___at___00tst3_spec__0_spec__0_spec__1(mut v_x_581_: *mut lean_object, mut v_x_582_: *mut lean_object) -> *mut lean_object{
let mut v_head_583_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_584_: *mut lean_object = core::ptr::null_mut(); let mut v___x_585_: *mut lean_object = core::ptr::null_mut(); let mut v___x_586_: *mut lean_object = core::ptr::null_mut(); let mut v___x_587_: f64 = 0.0; let mut v___x_588_: *mut lean_object = core::ptr::null_mut(); let mut v___x_589_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_582_) == 0 {
return v_x_581_;
} else {
v_head_583_ = lean_ctor_get(v_x_582_, 0);
v_tail_584_ = lean_ctor_get(v_x_582_, 1);
v___x_585_ = l_IO_println___at___00tst1_spec__7___closed__1;
v___x_586_ = lean_string_append(v_x_581_, v___x_585_);
v___x_587_ = lean_unbox_float(v_head_583_);
v___x_588_ = lean_float_to_string(v___x_587_);
v___x_589_ = lean_string_append(v___x_586_, v___x_588_);
lean_dec_ref(v___x_588_);
v_x_581_ = v___x_589_;
v_x_582_ = v_tail_584_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_foldl___at___00List_toString___at___00IO_println___at___00tst3_spec__0_spec__0_spec__1___boxed(mut v_x_591_: *mut lean_object, mut v_x_592_: *mut lean_object) -> *mut lean_object{
let mut v_res_593_: *mut lean_object = core::ptr::null_mut(); 
v_res_593_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00tst3_spec__0_spec__0_spec__1(v_x_591_, v_x_592_);
lean_dec(v_x_592_);
return v_res_593_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0(mut v_x_597_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_x_597_) == 0 {
let mut v___x_598_: *mut lean_object = core::ptr::null_mut(); 
v___x_598_ = l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0___closed__0;
return v___x_598_;
} else {
let mut v_tail_599_: *mut lean_object = core::ptr::null_mut(); 
v_tail_599_ = lean_ctor_get(v_x_597_, 1);
if lean_obj_tag(v_tail_599_) == 0 {
let mut v_head_600_: *mut lean_object = core::ptr::null_mut(); let mut v___x_601_: *mut lean_object = core::ptr::null_mut(); let mut v___x_602_: f64 = 0.0; let mut v___x_603_: *mut lean_object = core::ptr::null_mut(); let mut v___x_604_: *mut lean_object = core::ptr::null_mut(); let mut v___x_605_: *mut lean_object = core::ptr::null_mut(); let mut v___x_606_: *mut lean_object = core::ptr::null_mut(); 
v_head_600_ = lean_ctor_get(v_x_597_, 0);
v___x_601_ = l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0___closed__1;
v___x_602_ = lean_unbox_float(v_head_600_);
v___x_603_ = lean_float_to_string(v___x_602_);
v___x_604_ = lean_string_append(v___x_601_, v___x_603_);
lean_dec_ref(v___x_603_);
v___x_605_ = l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0___closed__2;
v___x_606_ = lean_string_append(v___x_604_, v___x_605_);
return v___x_606_;
} else {
let mut v_head_607_: *mut lean_object = core::ptr::null_mut(); let mut v___x_608_: *mut lean_object = core::ptr::null_mut(); let mut v___x_609_: f64 = 0.0; let mut v___x_610_: *mut lean_object = core::ptr::null_mut(); let mut v___x_611_: *mut lean_object = core::ptr::null_mut(); let mut v___x_612_: *mut lean_object = core::ptr::null_mut(); let mut v___x_613_: u32 = 0; let mut v___x_614_: *mut lean_object = core::ptr::null_mut(); 
v_head_607_ = lean_ctor_get(v_x_597_, 0);
v___x_608_ = l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0___closed__1;
v___x_609_ = lean_unbox_float(v_head_607_);
v___x_610_ = lean_float_to_string(v___x_609_);
v___x_611_ = lean_string_append(v___x_608_, v___x_610_);
lean_dec_ref(v___x_610_);
v___x_612_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00tst3_spec__0_spec__0_spec__1(v___x_611_, v_tail_599_);
v___x_613_ = 93;
v___x_614_ = lean_string_push(v___x_612_, v___x_613_);
return v___x_614_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0___boxed(mut v_x_615_: *mut lean_object) -> *mut lean_object{
let mut v_res_616_: *mut lean_object = core::ptr::null_mut(); 
v_res_616_ = l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0(v_x_615_);
lean_dec(v_x_615_);
return v_res_616_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst3_spec__0(mut v_s_617_: *mut lean_object) -> *mut lean_object{
let mut v___x_619_: *mut lean_object = core::ptr::null_mut(); let mut v___x_620_: u32 = 0; let mut v___x_621_: *mut lean_object = core::ptr::null_mut(); let mut v___x_622_: *mut lean_object = core::ptr::null_mut(); 
v___x_619_ = l_List_toString___at___00IO_println___at___00tst3_spec__0_spec__0(v_s_617_);
v___x_620_ = 10;
v___x_621_ = lean_string_push(v___x_619_, v___x_620_);
v___x_622_ = l_IO_print___at___00IO_println___at___00tst1_spec__0_spec__0(v___x_621_);
return v___x_622_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00tst3_spec__0___boxed(mut v_s_623_: *mut lean_object, mut v_a_624_: *mut lean_object) -> *mut lean_object{
let mut v_res_625_: *mut lean_object = core::ptr::null_mut(); 
v_res_625_ = l_IO_println___at___00tst3_spec__0(v_s_623_);
lean_dec(v_s_623_);
return v_res_625_;
}
#[no_mangle] pub unsafe extern "C" fn l_tst3(mut v_xs_626_: *mut lean_object, mut v_y_627_: f64) -> *mut lean_object{
let mut v___x_629_: *mut lean_object = core::ptr::null_mut(); let mut v___f_630_: *mut lean_object = core::ptr::null_mut(); let mut v___x_631_: *mut lean_object = core::ptr::null_mut(); let mut v___x_632_: *mut lean_object = core::ptr::null_mut(); 
v___x_629_ = lean_box_float(v_y_627_);
v___f_630_ = lean_alloc_closure(l_tst3___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_630_, 0, v___x_629_);
v___x_631_ = l_fMap(v___f_630_, v_xs_626_);
v___x_632_ = l_IO_println___at___00tst3_spec__0(v___x_631_);
lean_dec(v___x_631_);
return v___x_632_;
}
#[no_mangle] pub unsafe extern "C" fn l_tst3___boxed(mut v_xs_633_: *mut lean_object, mut v_y_634_: *mut lean_object, mut v_a_635_: *mut lean_object) -> *mut lean_object{
let mut v_y_boxed_636_: f64 = 0.0; let mut v_res_637_: *mut lean_object = core::ptr::null_mut(); 
v_y_boxed_636_ = lean_unbox_float(v_y_634_);
lean_dec_ref(v_y_634_);
v_res_637_ = l_tst3(v_xs_633_, v_y_boxed_636_);
return v_res_637_;
}
#[no_mangle] pub unsafe extern "C" fn l_tst4(mut v_xs_639_: *mut lean_object) -> *mut lean_object{
let mut v___f_641_: *mut lean_object = core::ptr::null_mut(); let mut v___x_642_: *mut lean_object = core::ptr::null_mut(); let mut v___x_643_: *mut lean_object = core::ptr::null_mut(); 
v___f_641_ = l_tst4___closed__0;
v___x_642_ = l_fMap(v___f_641_, v_xs_639_);
v___x_643_ = l_IO_println___at___00tst3_spec__0(v___x_642_);
lean_dec(v___x_642_);
return v___x_643_;
}
#[no_mangle] pub unsafe extern "C" fn l_tst4___boxed(mut v_xs_644_: *mut lean_object, mut v_a_645_: *mut lean_object) -> *mut lean_object{
let mut v_res_646_: *mut lean_object = core::ptr::null_mut(); 
v_res_646_ = l_tst4(v_xs_644_);
return v_res_646_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_647_: *mut lean_object) -> *mut lean_object{
let mut v___x_649_: u32 = 0; let mut v___x_650_: *mut lean_object = core::ptr::null_mut(); let mut v___x_651_: *mut lean_object = core::ptr::null_mut(); 
v___x_649_ = 10;
v___x_650_ = lean_string_push(v_s_647_, v___x_649_);
v___x_651_ = l_IO_print___at___00IO_println___at___00tst1_spec__0_spec__0(v___x_650_);
return v___x_651_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_652_: *mut lean_object, mut v_a_653_: *mut lean_object) -> *mut lean_object{
let mut v_res_654_: *mut lean_object = core::ptr::null_mut(); 
v_res_654_ = l_IO_println___at___00main_spec__0(v_s_652_);
return v_res_654_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> f64{
let mut v___x_656_: *mut lean_object = core::ptr::null_mut(); let mut v___x_657_: f64 = 0.0; 
v___x_656_ = lean_unsigned_to_nat(7);
v___x_657_ = lean_float_of_nat(v___x_656_);
return v___x_657_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> f64{
let mut v___x_658_: *mut lean_object = core::ptr::null_mut(); let mut v___x_659_: f64 = 0.0; 
v___x_658_ = lean_unsigned_to_nat(8);
v___x_659_ = lean_float_of_nat(v___x_658_);
return v___x_659_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__3() -> f64{
let mut v___x_660_: *mut lean_object = core::ptr::null_mut(); let mut v___x_661_: f64 = 0.0; 
v___x_660_ = lean_unsigned_to_nat(9);
v___x_661_ = lean_float_of_nat(v___x_660_);
return v___x_661_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__4() -> f64{
let mut v___x_662_: *mut lean_object = core::ptr::null_mut(); let mut v___x_663_: f64 = 0.0; 
v___x_662_ = lean_unsigned_to_nat(11);
v___x_663_ = lean_float_of_nat(v___x_662_);
return v___x_663_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__5___boxed__const__1() -> *mut lean_object{
let mut v___x_664_: f64 = 0.0; let mut v___x_665_: *mut lean_object = core::ptr::null_mut(); 
v___x_664_ = lean_float_once(core::ptr::addr_of_mut!(l_main___closed__4), core::ptr::addr_of_mut!(l_main___closed__4_once), _init_l_main___closed__4);
v___x_665_ = lean_box_float(v___x_664_);
return v___x_665_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__5() -> *mut lean_object{
let mut v___x_666_: *mut lean_object = core::ptr::null_mut(); let mut v___x_667_: *mut lean_object = core::ptr::null_mut(); let mut v___x_668_: *mut lean_object = core::ptr::null_mut(); 
v___x_666_ = lean_box(0);
v___x_667_ = l_main___closed__5___boxed__const__1;
v___x_668_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_ctor_set(v___x_668_, 1, v___x_666_);
return v___x_668_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__6___boxed__const__1() -> *mut lean_object{
let mut v___x_669_: f64 = 0.0; let mut v___x_670_: *mut lean_object = core::ptr::null_mut(); 
v___x_669_ = lean_float_once(core::ptr::addr_of_mut!(l_main___closed__3), core::ptr::addr_of_mut!(l_main___closed__3_once), _init_l_main___closed__3);
v___x_670_ = lean_box_float(v___x_669_);
return v___x_670_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__6() -> *mut lean_object{
let mut v___x_671_: *mut lean_object = core::ptr::null_mut(); let mut v___x_672_: *mut lean_object = core::ptr::null_mut(); let mut v___x_673_: *mut lean_object = core::ptr::null_mut(); 
v___x_671_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__5), core::ptr::addr_of_mut!(l_main___closed__5_once), _init_l_main___closed__5);
v___x_672_ = l_main___closed__6___boxed__const__1;
v___x_673_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___x_671_);
return v___x_673_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__7___boxed__const__1() -> *mut lean_object{
let mut v___x_674_: f64 = 0.0; let mut v___x_675_: *mut lean_object = core::ptr::null_mut(); 
v___x_674_ = lean_float_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v___x_675_ = lean_box_float(v___x_674_);
return v___x_675_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__7() -> *mut lean_object{
let mut v___x_676_: *mut lean_object = core::ptr::null_mut(); let mut v___x_677_: *mut lean_object = core::ptr::null_mut(); let mut v___x_678_: *mut lean_object = core::ptr::null_mut(); 
v___x_676_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__6), core::ptr::addr_of_mut!(l_main___closed__6_once), _init_l_main___closed__6);
v___x_677_ = l_main___closed__7___boxed__const__1;
v___x_678_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v___x_676_);
return v___x_678_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__8___boxed__const__1() -> *mut lean_object{
let mut v___x_679_: f64 = 0.0; let mut v___x_680_: *mut lean_object = core::ptr::null_mut(); 
v___x_679_ = lean_float_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_680_ = lean_box_float(v___x_679_);
return v___x_680_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__8() -> *mut lean_object{
let mut v___x_681_: *mut lean_object = core::ptr::null_mut(); let mut v___x_682_: *mut lean_object = core::ptr::null_mut(); let mut v___x_683_: *mut lean_object = core::ptr::null_mut(); 
v___x_681_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__7), core::ptr::addr_of_mut!(l_main___closed__7_once), _init_l_main___closed__7);
v___x_682_ = l_main___closed__8___boxed__const__1;
v___x_683_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_683_, 0, v___x_682_);
lean_ctor_set(v___x_683_, 1, v___x_681_);
return v___x_683_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__9___boxed__const__1() -> *mut lean_object{
let mut v___x_684_: f64 = 0.0; let mut v___x_685_: *mut lean_object = core::ptr::null_mut(); 
v___x_684_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__10), core::ptr::addr_of_mut!(l_tst1___closed__10_once), _init_l_tst1___closed__10);
v___x_685_ = lean_box_float(v___x_684_);
return v___x_685_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__9() -> *mut lean_object{
let mut v___x_686_: *mut lean_object = core::ptr::null_mut(); let mut v___x_687_: *mut lean_object = core::ptr::null_mut(); let mut v___x_688_: *mut lean_object = core::ptr::null_mut(); 
v___x_686_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__8), core::ptr::addr_of_mut!(l_main___closed__8_once), _init_l_main___closed__8);
v___x_687_ = l_main___closed__9___boxed__const__1;
v___x_688_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___x_686_);
return v___x_688_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__10___boxed__const__1() -> *mut lean_object{
let mut v___x_689_: f64 = 0.0; let mut v___x_690_: *mut lean_object = core::ptr::null_mut(); 
v___x_689_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__3), core::ptr::addr_of_mut!(l_tst1___closed__3_once), _init_l_tst1___closed__3);
v___x_690_ = lean_box_float(v___x_689_);
return v___x_690_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__10() -> *mut lean_object{
let mut v___x_691_: *mut lean_object = core::ptr::null_mut(); let mut v___x_692_: *mut lean_object = core::ptr::null_mut(); let mut v___x_693_: *mut lean_object = core::ptr::null_mut(); 
v___x_691_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__9), core::ptr::addr_of_mut!(l_main___closed__9_once), _init_l_main___closed__9);
v___x_692_ = l_main___closed__10___boxed__const__1;
v___x_693_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v___x_691_);
return v___x_693_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__11() -> f64{
let mut v___x_694_: f64 = 0.0; let mut v___x_695_: f64 = 0.0; 
v___x_694_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__3), core::ptr::addr_of_mut!(l_tst1___closed__3_once), _init_l_tst1___closed__3);
v___x_695_ = lean_float_negate(v___x_694_);
return v___x_695_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__12() -> *mut lean_object{
let mut v___x_696_: *mut lean_object = core::ptr::null_mut(); let mut v___x_697_: *mut lean_object = core::ptr::null_mut(); let mut v___x_698_: *mut lean_object = core::ptr::null_mut(); 
v___x_696_ = lean_box(0);
v___x_697_ = l_tst1___closed__88___boxed__const__1;
v___x_698_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___x_696_);
return v___x_698_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__13() -> *mut lean_object{
let mut v___x_699_: *mut lean_object = core::ptr::null_mut(); let mut v___x_700_: *mut lean_object = core::ptr::null_mut(); let mut v___x_701_: *mut lean_object = core::ptr::null_mut(); 
v___x_699_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__12), core::ptr::addr_of_mut!(l_main___closed__12_once), _init_l_main___closed__12);
v___x_700_ = l_tst1___closed__105___boxed__const__1;
v___x_701_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v___x_699_);
return v___x_701_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__14___boxed__const__1() -> *mut lean_object{
let mut v___x_702_: f64 = 0.0; let mut v___x_703_: *mut lean_object = core::ptr::null_mut(); 
v___x_702_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__79), core::ptr::addr_of_mut!(l_tst1___closed__79_once), _init_l_tst1___closed__79);
v___x_703_ = lean_box_float(v___x_702_);
return v___x_703_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__14() -> *mut lean_object{
let mut v___x_704_: *mut lean_object = core::ptr::null_mut(); let mut v___x_705_: *mut lean_object = core::ptr::null_mut(); let mut v___x_706_: *mut lean_object = core::ptr::null_mut(); 
v___x_704_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__13), core::ptr::addr_of_mut!(l_main___closed__13_once), _init_l_main___closed__13);
v___x_705_ = l_main___closed__14___boxed__const__1;
v___x_706_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v___x_704_);
return v___x_706_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__15___boxed__const__1() -> *mut lean_object{
let mut v___x_707_: f64 = 0.0; let mut v___x_708_: *mut lean_object = core::ptr::null_mut(); 
v___x_707_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__22), core::ptr::addr_of_mut!(l_tst1___closed__22_once), _init_l_tst1___closed__22);
v___x_708_ = lean_box_float(v___x_707_);
return v___x_708_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__15() -> *mut lean_object{
let mut v___x_709_: *mut lean_object = core::ptr::null_mut(); let mut v___x_710_: *mut lean_object = core::ptr::null_mut(); let mut v___x_711_: *mut lean_object = core::ptr::null_mut(); 
v___x_709_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__14), core::ptr::addr_of_mut!(l_main___closed__14_once), _init_l_main___closed__14);
v___x_710_ = l_main___closed__15___boxed__const__1;
v___x_711_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v___x_709_);
return v___x_711_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__16___boxed__const__1() -> *mut lean_object{
let mut v___x_712_: f64 = 0.0; let mut v___x_713_: *mut lean_object = core::ptr::null_mut(); 
v___x_712_ = lean_float_once(core::ptr::addr_of_mut!(l_main___closed__11), core::ptr::addr_of_mut!(l_main___closed__11_once), _init_l_main___closed__11);
v___x_713_ = lean_box_float(v___x_712_);
return v___x_713_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__16() -> *mut lean_object{
let mut v___x_714_: *mut lean_object = core::ptr::null_mut(); let mut v___x_715_: *mut lean_object = core::ptr::null_mut(); let mut v___x_716_: *mut lean_object = core::ptr::null_mut(); 
v___x_714_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__15), core::ptr::addr_of_mut!(l_main___closed__15_once), _init_l_main___closed__15);
v___x_715_ = l_main___closed__16___boxed__const__1;
v___x_716_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set(v___x_716_, 1, v___x_714_);
return v___x_716_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__17() -> *mut lean_object{
let mut v___x_717_: *mut lean_object = core::ptr::null_mut(); let mut v___x_718_: *mut lean_object = core::ptr::null_mut(); let mut v___x_719_: *mut lean_object = core::ptr::null_mut(); 
v___x_717_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__16), core::ptr::addr_of_mut!(l_main___closed__16_once), _init_l_main___closed__16);
v___x_718_ = l_main___closed__10___boxed__const__1;
v___x_719_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v___x_717_);
return v___x_719_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_721_: *mut lean_object = core::ptr::null_mut(); 
v___x_721_ = l_tst1();
if lean_obj_tag(v___x_721_) == 0 {
let mut v___x_722_: *mut lean_object = core::ptr::null_mut(); let mut v___x_723_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_721_, 1);
v___x_722_ = l_main___closed__0;
v___x_723_ = l_IO_println___at___00main_spec__0(v___x_722_);
if lean_obj_tag(v___x_723_) == 0 {
let mut v___x_724_: *mut lean_object = core::ptr::null_mut(); let mut v___x_725_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_723_, 1);
v___x_724_ = lean_unsigned_to_nat(7);
v___x_725_ = l_tst2(v___x_724_);
if lean_obj_tag(v___x_725_) == 0 {
let mut v___x_726_: *mut lean_object = core::ptr::null_mut(); let mut v___x_727_: f64 = 0.0; let mut v___x_728_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_725_, 1);
v___x_726_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__10), core::ptr::addr_of_mut!(l_main___closed__10_once), _init_l_main___closed__10);
v___x_727_ = lean_float_once(core::ptr::addr_of_mut!(l_tst1___closed__1), core::ptr::addr_of_mut!(l_tst1___closed__1_once), _init_l_tst1___closed__1);
v___x_728_ = l_tst3(v___x_726_, v___x_727_);
if lean_obj_tag(v___x_728_) == 0 {
let mut v___x_729_: *mut lean_object = core::ptr::null_mut(); let mut v___x_730_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_728_, 1);
v___x_729_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__17), core::ptr::addr_of_mut!(l_main___closed__17_once), _init_l_main___closed__17);
v___x_730_ = l_tst4(v___x_729_);
return v___x_730_;
} else {
return v___x_728_;
}
} else {
return v___x_725_;
}
} else {
return v___x_723_;
}
} else {
return v___x_721_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_731_: *mut lean_object) -> *mut lean_object{
let mut v_res_732_: *mut lean_object = core::ptr::null_mut(); 
v_res_732_ = _lean_main();
return v_res_732_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_float(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_tst1___closed__70___boxed__const__1 = _init_l_tst1___closed__70___boxed__const__1();
lean_mark_persistent(l_tst1___closed__70___boxed__const__1);
l_tst1___closed__78___boxed__const__1 = _init_l_tst1___closed__78___boxed__const__1();
lean_mark_persistent(l_tst1___closed__78___boxed__const__1);
l_tst1___closed__88___boxed__const__1 = _init_l_tst1___closed__88___boxed__const__1();
lean_mark_persistent(l_tst1___closed__88___boxed__const__1);
l_tst1___closed__96___boxed__const__1 = _init_l_tst1___closed__96___boxed__const__1();
lean_mark_persistent(l_tst1___closed__96___boxed__const__1);
l_tst1___closed__105___boxed__const__1 = _init_l_tst1___closed__105___boxed__const__1();
lean_mark_persistent(l_tst1___closed__105___boxed__const__1);
l_main___closed__5___boxed__const__1 = _init_l_main___closed__5___boxed__const__1();
lean_mark_persistent(l_main___closed__5___boxed__const__1);
l_main___closed__6___boxed__const__1 = _init_l_main___closed__6___boxed__const__1();
lean_mark_persistent(l_main___closed__6___boxed__const__1);
l_main___closed__7___boxed__const__1 = _init_l_main___closed__7___boxed__const__1();
lean_mark_persistent(l_main___closed__7___boxed__const__1);
l_main___closed__8___boxed__const__1 = _init_l_main___closed__8___boxed__const__1();
lean_mark_persistent(l_main___closed__8___boxed__const__1);
l_main___closed__9___boxed__const__1 = _init_l_main___closed__9___boxed__const__1();
lean_mark_persistent(l_main___closed__9___boxed__const__1);
l_main___closed__10___boxed__const__1 = _init_l_main___closed__10___boxed__const__1();
lean_mark_persistent(l_main___closed__10___boxed__const__1);
l_main___closed__14___boxed__const__1 = _init_l_main___closed__14___boxed__const__1();
lean_mark_persistent(l_main___closed__14___boxed__const__1);
l_main___closed__15___boxed__const__1 = _init_l_main___closed__15___boxed__const__1();
lean_mark_persistent(l_main___closed__15___boxed__const__1);
l_main___closed__16___boxed__const__1 = _init_l_main___closed__16___boxed__const__1();
lean_mark_persistent(l_main___closed__16___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_float(1 /* builtin */);
  lean_io_mark_end_initialization();
  let mut ret_val = 1;
  if lean_io_result_is_ok(res) {
    lean_dec(res);
    lean_init_task_manager();
    let main_res = lean_run_main(run_main, argc, argv);
    lean_finalize_task_manager();
    if lean_io_result_is_ok(main_res) {
      ret_val = 0;
      lean_dec(main_res);
    } else {
      lean_io_result_show_error(main_res);
      lean_dec(main_res);
    }
  } else {
    lean_io_result_show_error(res);
    lean_dec(res);
  }
  return ret_val;
}
