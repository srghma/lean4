#[repr(C)]
pub struct LeanObject {
    pub m_rc: i32,
    pub m_cs_sz: u16,
    pub m_other: u8,
    pub m_tag: u8,
}
#[repr(C)]
pub struct LeanStringObject {
    pub m_header: LeanObject,
    pub m_size: usize,
    pub m_capacity: usize,
    pub m_length: usize,
    pub m_data: [std::ffi::c_char; 0],
}
fn main() {
    println!("offset_of m_size: {}", core::mem::offset_of!(LeanStringObject, m_size));
    println!("offset_of m_capacity: {}", core::mem::offset_of!(LeanStringObject, m_capacity));
    println!("offset_of m_length: {}", core::mem::offset_of!(LeanStringObject, m_length));
    println!("offset_of m_data: {}", core::mem::offset_of!(LeanStringObject, m_data));
}
