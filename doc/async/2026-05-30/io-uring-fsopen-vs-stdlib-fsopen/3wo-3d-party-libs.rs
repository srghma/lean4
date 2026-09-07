use std::ffi::CString;
use std::os::raw::{c_int, c_long, c_uint};
use std::ptr;
use std::sync::atomic::{compiler_fence, Ordering};

// Native Linux System Call IDs for x86_64 architecture
const SYS_IO_URING_SETUP: c_long = 425;
const SYS_IO_URING_ENTER: c_long = 426;
const SYS_MMAP: c_long = 9;
const SYS_MUNMAP: c_long = 11;
const SYS_CLOSE: c_long = 3;

// io_uring Opcode and Constants
const IORING_OP_OPENAT: u8 = 18;
const AT_FDCWD: c_int = -100;
const O_RDONLY: c_int = 0;
const IORING_ENTER_GETEVENTS: c_uint = 1;

// Memory Ring Offsets for mmap
const IORING_OFF_SQ_RING: u64 = 0;
const IORING_OFF_CQ_RING: u64 = 0x8000000;
const IORING_OFF_SQES: u64 = 0x10000000;

// Protections and flags for memory allocation maps
const PROT_READ: c_int = 1;
const PROT_WRITE: c_int = 2;
const MAP_SHARED: c_int = 1;
const MAP_POPULATE: c_int = 0x08000;

// Native layout structures mirroring linux/io_uring.h exactly
#[repr(C)]
#[derive(Default, Debug)]
struct IoSqringOffsets {
    head: u32, tail: u32, ring_mask: u32, ring_entries: u32,
    flags: u32, dropped: u32, array: u32, resv1: u32, resv2: u64,
}

#[repr(C)]
#[derive(Default, Debug)]
struct IoCqringOffsets {
    head: u32, tail: u32, ring_mask: u32, ring_entries: u32,
    overflow: u32, cqes: u32, flags: u32, resv1: u32, resv2: u64,
}

#[repr(C)]
#[derive(Default, Debug)]
struct IoUringParams {
    sq_entries: u32, cq_entries: u32, flags: u32, sq_thread_cpu: u32,
    sq_thread_idle: u32, features: u32, wq_fd: u32, resv: [u32; 3],
    sq_off: IoSqringOffsets, cq_off: IoCqringOffsets,
}

#[repr(C)]
#[derive(Copy, Clone, Default)]
struct IoUringSqe {
    opcode: u8, flags: u8, ioprio: u16, fd: i32,
    off_or_addr2: u64, addr: u64, len: u32, open_flags: u32,
    user_data: u64, buf_index_or_group: u16, personality: u16,
    splice_fd_in_or_file_index: u32, addr3_or_pad: [u64; 2],
}

#[repr(C)]
#[derive(Copy, Clone, Default, Debug)]
struct IoUringCqe {
    user_data: u64,
    res: i32,
    flags: u32,
}

// Inline assembly wrappers to completely bypass external libraries
unsafe fn sys_io_uring_setup(entries: c_uint, params: *mut IoUringParams) -> c_int {
    let mut ret: c_long;
    std::arch::asm!(
        "syscall",
        in("rax") SYS_IO_URING_SETUP,
        in("rdi") entries,
        in("rsi") params,
        out("rcx") _, out("r11") _,
        lateout("rax") ret,
    );
    ret as c_int
}

unsafe fn sys_io_uring_enter(fd: c_int, to_submit: c_uint, min_complete: c_uint, flags: c_uint) -> c_int {
    let mut ret: c_long;
    std::arch::asm!(
        "syscall",
        in("rax") SYS_IO_URING_ENTER,
        in("rdi") fd,
        in("rsi") to_submit,
        in("rdx") min_complete,
        in("r10") flags,
        in("r8") ptr::null::<()>(),
        in("r9") 8usize,
        out("rcx") _, out("r11") _,
        lateout("rax") ret,
    );
    ret as c_int
}

unsafe fn sys_mmap(addr: *mut (), len: usize, prot: c_int, flags: c_int, fd: c_int, offset: u64) -> *mut () {
    let mut ret: *mut ();
    std::arch::asm!(
        "syscall",
        in("rax") SYS_MMAP,
        in("rdi") addr,
        in("rsi") len,
        in("rdx") prot,
        in("r10") flags,
        in("r8") fd,
        in("r9") offset,
        out("rcx") _, out("r11") _,
        lateout("rax") ret,
    );
    ret
}

fn main() {
    unsafe {
        let mut params = IoUringParams::default();

        // 1. Fire initialization system call
        let ring_fd = sys_io_uring_setup(1, &mut params);
        if ring_fd < 0 {
            panic!("io_uring_setup failed: {}", ring_fd);
        }

        // 2. Map structural sizes across ring bounds
        let sq_ring_sz = (params.sq_off.array + params.sq_entries * 4) as usize;
        let cq_ring_sz = (params.cq_off.cqes + params.cq_entries * std::mem::size_of::<IoUringCqe>() as u32) as usize;

        let sq_ptr = sys_mmap(ptr::null_mut(), sq_ring_sz, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring_fd, IORING_OFF_SQ_RING);
        let sqes_ptr = sys_mmap(ptr::null_mut(), (params.sq_entries as usize) * std::mem::size_of::<IoUringSqe>(), PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring_fd, IORING_OFF_SQES) as *mut IoUringSqe;
        let cq_ptr = sys_mmap(ptr::null_mut(), cq_ring_sz, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring_fd, IORING_OFF_CQ_RING);

        // 3. Resolve raw data offset pointer positions
        let sq_tail_ptr = sq_ptr.add(params.sq_off.tail as usize) as *mut c_uint;
        let sq_mask = *(sq_ptr.add(params.sq_off.ring_mask as usize) as *const c_uint);
        let sq_array_ptr = sq_ptr.add(params.sq_off.array as usize) as *mut c_uint;

        let cq_head_ptr = cq_ptr.add(params.cq_off.head as usize) as *mut c_uint;
        let cq_tail_ptr = cq_ptr.add(params.cq_off.tail as usize) as *const c_uint;
        let cq_mask = *(cq_ptr.add(params.cq_off.ring_mask as usize) as *const c_uint);
        let cqes_ptr = cq_ptr.add(params.cq_off.cqes as usize) as *const IoUringCqe;

        // 4. Construct the asynchronous open configuration manually
        let path = CString::new("example.txt").unwrap();
        let tail = *sq_tail_ptr;
        let index = (tail & sq_mask) as usize;

        let sqe = &mut *sqes_ptr.add(index);
        *sqe = IoUringSqe::default();
        sqe.opcode = IORING_OP_OPENAT;
        sqe.fd = AT_FDCWD;
        sqe.addr = path.as_ptr() as u64;
        sqe.open_flags = O_RDONLY as u32;
        sqe.user_data = 1337;

        *sq_array_ptr.add(index) = index as c_uint;
        *sq_tail_ptr = tail + 1;
        compiler_fence(Ordering::Release); // Ensure memory order consistency before submission

        // 5. Signal the kernel to ingest execution queue entries
        let entered = sys_io_uring_enter(ring_fd, 1, 1, IORING_ENTER_GETEVENTS);
        if entered < 0 {
            panic!("io_uring_enter execution failure: {}", entered);
        }

        // 6. Pull completion tracking items from loop buffers safely
        compiler_fence(Ordering::Acquire);
        let head = *cq_head_ptr;
        if head != *cq_tail_ptr {
            let cqe = &*cqes_ptr.add((head & cq_mask) as usize);
            let file_fd = cqe.res;

            if file_fd < 0 {
                println!("Failed opening via raw Rust io_uring. Kernel Error Code: {}", file_fd);
            } else {
                println!("Successfully opened file inside raw Rust context! FD allocated: {}", file_fd);
                std::arch::asm!("syscall", in("rax") SYS_CLOSE, in("rdi") file_fd, out("rcx") _, out("r11") _,);
            }
            *cq_head_ptr = head + 1;
            compiler_fence(Ordering::Release);
        }

        // 7. Free layout map registers back to kernel regions
        std::arch::asm!("syscall", in("rax") SYS_MUNMAP, in("rdi") sq_ptr, in("rsi") sq_ring_sz, out("rcx") _, out("r11") _,);
        std::arch::asm!("syscall", in("rax") SYS_MUNMAP, in("rdi") sqes_ptr, in("rsi") (params.sq_entries as usize) * std::mem::size_of::<IoUringSqe>(), out("rcx") _, out("r11") _,);
        std::arch::asm!("syscall", in("rax") SYS_MUNMAP, in("rdi") cq_ptr, in("rsi") cq_ring_sz, out("rcx") _, out("r11") _,);
        std::arch::asm!("syscall", in("rax") SYS_CLOSE, in("rdi") ring_fd, out("rcx") _, out("r11") _,);
    }
}
