#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <linux/io_uring.h>

// Fixed for Clang compatibility: Both barriers now use the universal compiler built-in
#define read_barrier()  __sync_synchronize() // __kernel_cmpxchg()
#define write_barrier() __sync_synchronize()

// Manually defining the raw Linux system calls
static int io_uring_setup(unsigned entries, struct io_uring_params *p) {
    return syscall(SYS_io_uring_setup, entries, p);
}

static int io_uring_enter(int fd, unsigned to_submit, unsigned min_complete, unsigned flags, sigset_t *sig) {
    // Explicit typecast to suppress Clang warnings about parameter pointer sizing
    return syscall(SYS_io_uring_enter, fd, to_submit, min_complete, flags, sig, 8);
}

int main() {
    struct io_uring_params p;
    memset(&p, 0, sizeof(p));

    // 1. Initialize io_uring instance via native system call
    int ring_fd = io_uring_setup(1, &p);
    if (ring_fd < 0) {
        perror("io_uring_setup");
        return 1;
    }

    // 2. Map Submission Queue (SQ) and Completion Queue (CQ) memory regions from kernel space
    int sq_ring_sz = p.sq_off.array + p.sq_entries * sizeof(unsigned);
    int cq_ring_sz = p.cq_off.cqes + p.cq_entries * sizeof(struct io_uring_cqe);

    // Map single memory region for SQ rings, fields, and indices
    void *sq_ptr = mmap(0, sq_ring_sz, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring_fd, IORING_OFF_SQ_RING);
    // Map memory region for SQ Es (Submission Queue Entries)
    struct io_uring_sqe *sqes = mmap(0, p.sq_entries * sizeof(struct io_uring_sqe), PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring_fd, IORING_OFF_SQES);
    // Map memory region for CQEs (Completion Queue Entries)
    void *cq_ptr = mmap(0, cq_ring_sz, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring_fd, IORING_OFF_CQ_RING);

    if (sq_ptr == MAP_FAILED || sqes == MAP_FAILED || cq_ptr == MAP_FAILED) {
        perror("mmap");
        return 1;
    }

    // 3. Set up pointers to index variables inside the mapped memory regions
    unsigned *sq_head  = (unsigned *)(sq_ptr + p.sq_off.head);
    unsigned *sq_tail  = (unsigned *)(sq_ptr + p.sq_off.tail);
    unsigned *sq_mask  = (unsigned *)(sq_ptr + p.sq_off.ring_mask);
    unsigned *sq_array = (unsigned *)(sq_ptr + p.sq_off.array);

    unsigned *cq_head  = (unsigned *)(cq_ptr + p.cq_off.head);
    unsigned *cq_tail  = (unsigned *)(cq_ptr + p.cq_off.tail);
    unsigned *cq_mask  = (unsigned *)(cq_ptr + p.cq_off.ring_mask);
    struct io_uring_cqe *cqes = (struct io_uring_cqe *)(cq_ptr + p.cq_off.cqes);

    // 4. Populate a raw SQE to open the file
    unsigned tail = *sq_tail;
    unsigned index = tail & *sq_mask;
    struct io_uring_sqe *sqe = &sqes[index];

    memset(sqe, 0, sizeof(*sqe));
    sqe->opcode = IORING_OP_OPENAT; // Native opcode for opening files
    sqe->fd = AT_FDCWD;
    sqe->addr = (unsigned long)"example.txt";
    sqe->open_flags = O_RDONLY;
    sqe->user_data = 42;            // Custom tracking tag

    // 5. Update submission queue tail and notify kernel
    sq_array[index] = index;
    *sq_tail = tail + 1;
    write_barrier(); // Prevent memory reordering before the system call

    // Submit 1 event and block until at least 1 event completes
    if (io_uring_enter(ring_fd, 1, 1, IORING_ENTER_GETEVENTS, NULL) < 0) {
        perror("io_uring_enter");
        return 1;
    }

    // 6. Read results out from the raw Completion Queue
    read_barrier(); // Ensure we read fresh memory populated by the kernel
    unsigned head = *cq_head;
    if (head != *cq_tail) {
        struct io_uring_cqe *cqe = &cqes[head & *cq_mask];

        int file_fd = cqe->res;
        if (file_fd < 0) {
            fprintf(stderr, "Failed to open file: %s\n", strerror(-file_fd));
        } else {
            printf("Successfully opened file using Clang and raw syscalls! FD: %d\n", file_fd);
            close(file_fd);
        }

        // Advance head pointer to let kernel know we processed the result
        *cq_head = head + 1;
        write_barrier();
    }

    // 7. Cleanup resource mapping
    munmap(sq_ptr, sq_ring_sz);
    munmap(sqes, p.sq_entries * sizeof(struct io_uring_sqe));
    munmap(cq_ptr, cq_ring_sz);
    close(ring_fd);

    return 0;
}
