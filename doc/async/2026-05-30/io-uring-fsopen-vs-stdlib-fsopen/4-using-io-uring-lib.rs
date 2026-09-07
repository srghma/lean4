use io_uring::{opcode, types, IoUring};
use std::fs::File;
use std::os::unix::io::AsRawFd;
use std::os::unix::prelude::RawFd;

fn main() -> std::io::Result<()> {
    // 1. Initialize io_uring engine instance (handles setups & mmaps safely)
    let mut ring = IoUring::new(1)?;

    // 2. Prepare the target filename tracking criteria
    // We use standard Rust paths/strings as the library safely borrows them
    let filename = std::ffi::CString::new("example.txt").unwrap();

    // 3. Build the openat operational entry
    // types::Fd(libc::AT_FDCWD) tells the kernel to look in the current working directory
    let open_op = opcode::OpenAt::new(types::Fd(libc::AT_FDCWD), filename.as_ptr())
        .flags(libc::O_RDONLY)
        .build()
        .user_data(1337); // Tag your tracking identity

    // 4. Push entry onto the submission queue safely
    unsafe {
        ring.submission()
            .push(&open_op)
            .expect("submission queue is full");
    }

    // 5. Submit the operations and block until at least one event completes
    ring.submit_and_wait(1)?;

    // 6. Consume results out from the completion queue
    let mut cq = ring.completion();
    if let Some(cqe) = cq.next() {
        // Double check this is the entry we submitted
        assert_eq!(cqe.user_data(), 1337);

        let result_fd = cqe.result();
        if result_fd < 0 {
            // Kernel returns negative values for standard system errors
            let err = std::io::Error::from_raw_os_error(-result_fd);
            println!("Failed to open file via io-uring crate: {}", err);
        } else {
            let file_fd: RawFd = result_fd;
            println!("Successfully opened file inside safe Rust! FD allocated: {}", file_fd);

            // Idiomatic Rust conversion: wrap the raw descriptor into a managed standard File type
            // This ensures standard safety rules apply and drops/closes the file when out of scope
            unsafe {
                let _file = File::from_raw_fd(file_fd);
                // Do synchronous or chained asynchronous reads using `_file` here...
            }
        }
    }

    // Standard RAII cleanup: when `ring` leaves scope, it drops and frees kernel maps natively
    Ok(())
}
