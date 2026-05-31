#include <stdio.h>
#include <fcntl.h>
#include <string.h>
#include <liburing.h>

#define QUEUE_DEPTH 1

int main() {
    struct io_uring ring;
    struct io_uring_sqe *sqe;
    struct io_uring_cqe *cqe;

    // 1. Initialize the io_uring instance
    if (io_uring_queue_init(QUEUE_DEPTH, &ring, 0) < 0) {
        perror("io_uring_queue_init");
        return 1;
    }

    // 2. Get a Submission Queue Entry (SQE)
    sqe = io_uring_get_sqe(&ring);
    if (!sqe) {
        fprintf(stderr, "Could not get SQE\n");
        return 1;
    }

    // 3. Prepare the open operation (equivalent to openat)
    const char *filename = "example.txt";
    int flags = O_RDONLY;
    mode_t mode = 0;

    // AT_FDCWD specifies to look for the file relative to the current working directory
    io_uring_prep_openat(sqe, AT_FDCWD, filename, flags, mode);

    // Optional: Tag the SQE with user data to identify it upon completion
    unsigned long long custom_id = 42;
    io_uring_sqe_set_data(sqe, (void *)custom_id);

    // 4. Submit the entry to the kernel and wait for completion
    io_uring_submit(&ring);

    if (io_uring_wait_cqe(&ring, &cqe) < 0) {
        perror("io_uring_wait_cqe");
        return 1;
    }

    // 5. Read the result from the Completion Queue Entry (CQE)
    // For open operations, cqe->res contains the File Descriptor (or negative error code)
    int file_fd = cqe->res;
    if (file_fd < 0) {
        fprintf(stderr, "Failed to open file: %s\n", strerror(-file_fd));
    } else {
        printf("Successfully opened file! FD assigned: %d\n", file_fd);

        // Use the file_fd for subsequent reads/writes here...

        close(file_fd);
    }

    // 6. Clear out the completed item and clean up the ring
    io_uring_cqe_seen(&ring, cqe);
    io_uring_queue_exit(&ring);

    return 0;
}
