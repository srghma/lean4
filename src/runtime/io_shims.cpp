/*
 * io_shims.cpp
 *
 * Thin C wrappers that bridge runtime_io.rs to C++ APIs that Rust cannot
 * call directly (template methods, platform-specific APIs, C++ exceptions,
 * atomic<object*>, etc.).
 *
 * Place in src/runtime/ and add to RUNTIME_OBJS in CMakeLists.txt.
 *
 * When io.cpp is removed from RUNTIME_OBJS, remove the corresponding
 * LEAN_EXPORT functions from io.cpp or guard them with
 * #ifndef LEAN_RUST_IO.
 */

#if defined(LEAN_WINDOWS)
#  include <icu.h>
#  include <windows.h>
#  include <io.h>
#  define NOMINMAX
#  include <ntdef.h>
#  include <bcrypt.h>
#elif defined(__APPLE__)
#  include <mach-o/dyld.h>
#  include <unistd.h>
#else
#  include <unistd.h>
#  include <sys/file.h>
#  ifndef LEAN_EMSCRIPTEN
#    include <sys/random.h>
#  endif
#endif

#include <csignal>
#include <cstring>
#include <cstdio>
#include <cstdlib>
#include <cctype>
#include <climits>
#include <atomic>
#include <uv.h>
#include <lean/lean.h>
#include "runtime/io.h"
#include "runtime/object.h"
#include "runtime/thread.h"
#include "runtime/object_ref.h"
#include "runtime/option_ref.h"
#include <cerrno>

using namespace lean;

extern "C" {
lean_object * lean_io_prim_handle_lock(lean_object * h, uint8_t x);
lean_object * lean_io_prim_handle_try_lock(lean_object * h, uint8_t x);
lean_object * lean_io_prim_handle_unlock(lean_object * h);
lean_object * lean_io_prim_handle_mk(lean_object * filename, uint8_t mode);
lean_object * lean_io_as_task(lean_object * act, lean_object * prio);
lean_object * lean_io_map_task(lean_object * f, lean_object * t, lean_object * prio, uint8_t sync);
lean_object * lean_io_bind_task(lean_object * t, lean_object * f, lean_object * prio, uint8_t sync);
lean_object * lean_decode_io_error_c(int errnum, lean_object * fname);
}

static lean_object * mk_file_not_found_error(lean_object * fname) {
    return lean_decode_io_error_c(ENOENT, fname);
}

// ---------------------------------------------------------------------------
// libc pass-throughs (Rust calls these as extern "C")
// ---------------------------------------------------------------------------
extern "C" {
    size_t libc_strlen(const char * s) { return strlen(s); }
    const char * libc_strerror(int e) { return strerror(e); }
    int libc_fclose(FILE * fp) { return fclose(fp); }
    int libc_fflush(FILE * fp) { return fflush(fp); }
    int libc_fseek(FILE * fp, int64_t off, int w) { return fseek(fp, off, w); }
    size_t libc_fread(uint8_t * buf, size_t sz, size_t n, FILE * fp) { return fread(buf, sz, n, fp); }
    size_t libc_fwrite(const uint8_t * buf, size_t sz, size_t n, FILE * fp) { return fwrite(buf, sz, n, fp); }
    int libc_feof(FILE * fp) { return feof(fp); }
    int libc_ferror(FILE * fp) { return ferror(fp); }
    void libc_clearerr(FILE * fp) { clearerr(fp); }
    int libc_isatty(int fd) { return isatty(fd); }
    int libc_fileno(FILE * fp) { return fileno(fp); }
    int64_t libc_ftello(FILE * fp) { return (int64_t)ftello(fp); }
    int libc_ftruncate(int fd, int64_t len) { return ftruncate(fd, len); }
    char * libc_getcwd(char * buf, size_t sz) { return getcwd(buf, sz); }
    int libc_open(const char * path, int flags, int mode) { return open(path, flags, mode); }
    FILE * libc_fdopen_with_mode(int fd, const char * mode) { return fdopen(fd, mode); }
    int libc_mkdir(const char * path, int mode) {
#ifdef LEAN_WINDOWS
        return mkdir(path);
#else
        return mkdir(path, mode);
#endif
    }
    int libc_rmdir(const char * path) { return rmdir(path); }
    int libc_rename(const char * a, const char * b) { return rename(a, b); }
    int libc_chmod(const char * path, unsigned mode) { return chmod(path, mode); }
    int libc_flock(int fd, int op) {
#ifdef LEAN_WINDOWS
        (void)fd; (void)op; return 0;
#else
        return ::flock(fd, op);
#endif
    }
    int libc_getc_unlocked(FILE * fp) {
#ifdef LEAN_WINDOWS
        return _fgetc_nolock(fp);
#else
        return getc_unlocked(fp);
#endif
    }
    void libc_flockfile(FILE * fp) {
#ifdef LEAN_WINDOWS
        _lock_file(fp);
#else
        flockfile(fp);
#endif
    }
    void libc_funlockfile(FILE * fp) {
#ifdef LEAN_WINDOWS
        _unlock_file(fp);
#else
        funlockfile(fp);
#endif
    }
    char * libc_realpath(const char * path, char * out) {
#ifdef LEAN_WINDOWS
        (void)path; (void)out; return nullptr;
#else
        return realpath(path, out);
#endif
    }
    int libc_getpid() { return (int)getpid(); }
    ssize_t libc_readlink(const char * path, char * buf, size_t sz) {
#ifdef LEAN_WINDOWS
        (void)path; (void)buf; (void)sz; return -1;
#else
        return readlink(path, buf, sz);
#endif
    }
    ssize_t libc_read_urandom(uint8_t * buf, size_t n) {
#ifdef LEAN_WINDOWS
        (void)buf; (void)n; return -1;
#elif defined(LEAN_EMSCRIPTEN)
        // use getrandom fallback
        (void)buf; (void)n; return -1;
#else
        static int fd_urandom = -1;
        if (fd_urandom < 0) fd_urandom = open("/dev/urandom", O_RDONLY | O_CLOEXEC);
        if (fd_urandom < 0) return -1;
        return read(fd_urandom, buf, n);
#endif
    }
    // opendir / readdir / closedir
    void * libc_opendir(const char * path) { return opendir(path); }
    struct dirent * libc_readdir(void * dp) { return readdir((DIR*)dp); }
    int libc_closedir(void * dp) { return closedir((DIR*)dp); }

    int lean_errno() { return errno; }
    FILE * lean_io_shim_stderr() { return stderr; }

    int fputs(const char * s, FILE * fp);
} // extern "C"

// ---------------------------------------------------------------------------
// Stream thread-locals
// ---------------------------------------------------------------------------
MK_THREAD_LOCAL_GET(object_ref, get_stream_current_stdin,  (lean_object*)nullptr);
MK_THREAD_LOCAL_GET(object_ref, get_stream_current_stdout, (lean_object*)nullptr);
MK_THREAD_LOCAL_GET(object_ref, get_stream_current_stderr, (lean_object*)nullptr);

extern "C" {

lean_object * lean_io_shim_get_stdin()  { return get_stream_current_stdin().to_obj_arg(); }
lean_object * lean_io_shim_get_stdout() { return get_stream_current_stdout().to_obj_arg(); }
lean_object * lean_io_shim_get_stderr() { return get_stream_current_stderr().to_obj_arg(); }

lean_object * lean_io_shim_set_stdin(lean_object * h) {
    object_ref & x = get_stream_current_stdin(); lean_object * r = x.steal(); x = object_ref(h); return r;
}
lean_object * lean_io_shim_set_stdout(lean_object * h) {
    object_ref & x = get_stream_current_stdout(); lean_object * r = x.steal(); x = object_ref(h); return r;
}
lean_object * lean_io_shim_set_stderr(lean_object * h) {
    object_ref & x = get_stream_current_stderr(); lean_object * r = x.steal(); x = object_ref(h); return r;
}

// ---------------------------------------------------------------------------
// io_wrap_handle / io_get_handle via existing external class
// ---------------------------------------------------------------------------
lean_object * lean_io_wrap_handle_c(FILE * fp) { return io_wrap_handle(fp); }
FILE * lean_io_get_handle_c(lean_object * h) {
    return static_cast<FILE *>(lean_get_external_data(h));
}

// ---------------------------------------------------------------------------
// initialize: register external class + global streams + signal mask
// ---------------------------------------------------------------------------
void lean_io_shim_init() {
    initialize_io();
}

// ---------------------------------------------------------------------------
// IO error helpers
// ---------------------------------------------------------------------------
lean_object * lean_decode_io_error_c(int errnum, lean_object * fname) {
    return lean_decode_io_error(errnum, fname);
}
lean_object * lean_decode_uv_error_c(int errnum, lean_object * fname) {
    return lean_decode_uv_error(errnum, fname);
}
lean_object * lean_mk_embedded_nul_error_c(lean_object * s) {
    return mk_embedded_nul_error(s);
}

// ---------------------------------------------------------------------------
// Handle lock/unlock (platform-specific)
// ---------------------------------------------------------------------------
lean_object * lean_io_shim_handle_lock(lean_object * h, uint8_t x) {
    return ::lean_io_prim_handle_lock(h, x);
}
lean_object * lean_io_shim_handle_try_lock(lean_object * h, uint8_t x) {
    return ::lean_io_prim_handle_try_lock(h, x);
}
lean_object * lean_io_shim_handle_unlock(lean_object * h) {
    return ::lean_io_prim_handle_unlock(h);
}

// ---------------------------------------------------------------------------
// open handle — delegates to existing C++ impl which knows platform O_ flags
// ---------------------------------------------------------------------------
lean_object * lean_io_shim_open_handle(const char * path, uint8_t mode) {
    lean_object * fname_obj = lean_mk_string(path);
    lean_object * result = ::lean_io_prim_handle_mk(fname_obj, mode);
    lean_dec(fname_obj);
    return result;
}

// ---------------------------------------------------------------------------
// uv wrappers
// ---------------------------------------------------------------------------
static void copy_stat(uv_stat_t const & s, void * out) {
    // Mirror struct layout from runtime_io.rs UvStatBuf
    struct RustUvStatBuf {
        uint64_t st_dev, st_mode, st_nlink, st_uid, st_gid, st_rdev, st_ino;
        uint64_t st_size, st_blksize, st_blocks, st_flags, st_gen;
        struct { int64_t tv_sec; uint32_t tv_nsec; } st_atim, st_mtim, st_ctim, st_birthtim;
    };
    RustUvStatBuf * r = static_cast<RustUvStatBuf *>(out);
    r->st_dev   = s.st_dev;   r->st_mode  = s.st_mode;  r->st_nlink = s.st_nlink;
    r->st_uid   = s.st_uid;   r->st_gid   = s.st_gid;   r->st_rdev  = s.st_rdev;
    r->st_ino   = s.st_ino;   r->st_size  = s.st_size;
    r->st_blksize = s.st_blksize; r->st_blocks = s.st_blocks;
    r->st_flags = s.st_flags; r->st_gen   = s.st_gen;
    r->st_atim  = { s.st_atim.tv_sec,  (uint32_t)s.st_atim.tv_nsec };
    r->st_mtim  = { s.st_mtim.tv_sec,  (uint32_t)s.st_mtim.tv_nsec };
    r->st_ctim  = { s.st_ctim.tv_sec,  (uint32_t)s.st_ctim.tv_nsec };
    r->st_birthtim = { s.st_birthtim.tv_sec, (uint32_t)s.st_birthtim.tv_nsec };
}

int lean_io_shim_uv_stat(const char * path, void * out) {
    uv_fs_t req;
    int ret = uv_fs_stat(NULL, &req, path, NULL);
    if (ret >= 0) copy_stat(req.statbuf, out);
    uv_fs_req_cleanup(&req);
    return ret;
}

int lean_io_shim_uv_lstat(const char * path, void * out) {
    uv_fs_t req;
    int ret = uv_fs_lstat(NULL, &req, path, NULL);
    if (ret >= 0) copy_stat(req.statbuf, out);
    uv_fs_req_cleanup(&req);
    return ret;
}

int lean_io_shim_uv_link(const char * orig, const char * link) {
    uv_fs_t req;
    int ret = uv_fs_link(NULL, &req, orig, link, NULL);
    uv_fs_req_cleanup(&req);
    return ret;
}

int lean_io_shim_uv_unlink(const char * path) {
    uv_fs_t req;
    int ret = uv_fs_unlink(NULL, &req, path, NULL);
    uv_fs_req_cleanup(&req);
    return ret;
}

const char * lean_io_shim_uv_strerror(int e) { return uv_strerror(e); }

int lean_io_shim_uv_os_tmpdir(char * buf, size_t * sz) {
    return uv_os_tmpdir(buf, sz);
}

int lean_io_shim_uv_fs_mkstemp(const char * pattern, int * out_fd, char * out_path, size_t path_cap) {
    char buf[4096];
    if (strlen(pattern) >= sizeof(buf)) return UV_ENAMETOOLONG;
    strcpy(buf, pattern);
    uv_fs_t req;
    int ret = uv_fs_mkstemp(NULL, &req, buf, NULL);
    if (ret >= 0) {
        *out_fd = (int)req.result;
        strncpy(out_path, req.path, path_cap - 1);
        out_path[path_cap - 1] = '\0';
    }
    uv_fs_req_cleanup(&req);
    return ret;
}

int lean_io_shim_uv_fs_mkdtemp(const char * pattern, char * out_path, size_t path_cap) {
    char buf[4096];
    if (strlen(pattern) >= sizeof(buf)) return UV_ENAMETOOLONG;
    strcpy(buf, pattern);
    uv_fs_t req;
    int ret = uv_fs_mkdtemp(NULL, &req, buf, NULL);
    if (ret >= 0) {
        strncpy(out_path, req.path, path_cap - 1);
        out_path[path_cap - 1] = '\0';
    }
    uv_fs_req_cleanup(&req);
    return ret;
}

// ---------------------------------------------------------------------------
// app_path (platform-specific)
// ---------------------------------------------------------------------------
lean_object * lean_io_shim_app_path() {
#ifdef LEAN_WINDOWS
    char path[MAX_PATH];
    GetModuleFileName(GetModuleHandle(NULL), path, MAX_PATH);
    if (strlen(path) >= 2 && path[1] == ':') path[0] = tolower(path[0]);
    return io_result_mk_ok(mk_string(path));
#elif defined(__APPLE__)
    char buf1[PATH_MAX], buf2[PATH_MAX];
    uint32_t sz = PATH_MAX;
    if (_NSGetExecutablePath(buf1, &sz) != 0) return io_result_mk_error("failed to locate application");
    if (!realpath(buf1, buf2)) return io_result_mk_error("failed to resolve symbolic links when locating application");
    return io_result_mk_ok(mk_string(buf2));
#elif defined(LEAN_EMSCRIPTEN)
    return io_result_mk_error("no Lean executable file exists in WASM outside of Node.js");
#else
    char path[PATH_MAX], dest[PATH_MAX];
    memset(dest, 0, PATH_MAX);
    pid_t pid = getpid();
    snprintf(path, PATH_MAX, "/proc/%d/exe", pid);
    if (readlink(path, dest, PATH_MAX - 1) == -1)
        return io_result_mk_error("failed to locate application");
    return io_result_mk_ok(mk_string(dest));
#endif
}

// ---------------------------------------------------------------------------
// realpath
// ---------------------------------------------------------------------------
lean_object * lean_io_shim_realpath(const char * path) {
#ifdef LEAN_WINDOWS
    constexpr unsigned BufferSize = 8192;
    char buffer[BufferSize];
    HANDLE handle = CreateFile(path, 0, FILE_SHARE_READ, NULL, OPEN_EXISTING, FILE_FLAG_BACKUP_SEMANTICS, NULL);
    if (handle == INVALID_HANDLE_VALUE) {
        lean_object * fn = lean_mk_string(path);
        lean_object * r = mk_file_not_found_error(fn);
        lean_dec(fn);
        return r;
    }
    DWORD retval = GetFinalPathNameByHandle(handle, buffer, BufferSize, 0);
    CloseHandle(handle);
    if (retval == 0 || retval > BufferSize)
        return io_result_mk_ok(lean_mk_string(path));
    char * res = buffer;
    if (memcmp(res, "\\\\?\\", 4) == 0) {
        if (memcmp(res + 4, "UNC\\", 4) == 0) { res[6] = '\\'; res += 6; }
        else res += 4;
    }
    if (strlen(res) >= 2 && res[1] == ':') res[0] = tolower(res[0]);
    return io_result_mk_ok(mk_string(res));
#else
    char buffer[PATH_MAX];
    char * tmp = realpath(path, buffer);
    if (tmp) return io_result_mk_ok(mk_string(tmp));
    lean_object * fn = lean_mk_string(path);
    lean_object * r = mk_file_not_found_error(fn);
    lean_dec(fn);
    return r;
#endif
}

// ---------------------------------------------------------------------------
// rename (platform-aware)
// ---------------------------------------------------------------------------
lean_object * lean_io_shim_rename(const char * from, const char * to) {
#ifdef LEAN_WINDOWS
    if (!MoveFileEx(from, to, MOVEFILE_REPLACE_EXISTING)) {
        char msg[256];
        snprintf(msg, sizeof(msg), "failed to rename '%s' to '%s': %lu", from, to, GetLastError());
        return io_result_mk_error(msg);
    }
    return io_result_mk_ok(lean_box(0));
#else
    if (rename(from, to) == 0) return io_result_mk_ok(lean_box(0));
    char combined[PATH_MAX * 2 + 8];
    snprintf(combined, sizeof(combined), "%s and/or %s", from, to);
    lean_object * fn = lean_mk_string(combined);
    lean_object * r = io_result_mk_error(decode_io_error(errno, fn));
    lean_dec(fn);
    return r;
#endif
}

// ---------------------------------------------------------------------------
// handle_mk via C string (avoids re-boxing)
// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
// MT ref helpers (need std::atomic)
// ---------------------------------------------------------------------------
static inline std::atomic<lean_object*> * mt_ref_val_addr(lean_object * o) {
    return reinterpret_cast<std::atomic<lean_object*>*>(&lean_to_ref(o)->m_value);
}

lean_object * lean_io_shim_ref_get_mt(lean_object * ref) {
    auto * val_addr = mt_ref_val_addr(ref);
    while (true) {
        lean_object * val = val_addr->exchange(nullptr);
        if (val != nullptr) {
            inc(val);
            lean_object * tmp = val_addr->exchange(val);
            if (tmp != nullptr) dec(tmp);
            return val;
        }
    }
}

lean_object * lean_io_shim_ref_take_mt(lean_object * ref) {
    auto * val_addr = mt_ref_val_addr(ref);
    while (true) {
        lean_object * val = val_addr->exchange(nullptr);
        if (val != nullptr) return val;
    }
}

void lean_io_shim_ref_set_mt(lean_object * ref, lean_object * a) {
    auto * val_addr = mt_ref_val_addr(ref);
    lean_object * old = val_addr->exchange(a);
    if (old != nullptr) dec(old);
}

lean_object * lean_io_shim_ref_swap_mt(lean_object * ref, lean_object * a) {
    auto * val_addr = mt_ref_val_addr(ref);
    while (true) {
        lean_object * old = val_addr->exchange(a);
        if (old != nullptr) return old;
    }
}

// ---------------------------------------------------------------------------
// task combinators (thin wrappers around task_*.cpp symbols)
// ---------------------------------------------------------------------------
lean_object * lean_io_as_task_core(lean_object * act, size_t prio) {
    return ::lean_io_as_task(act, lean_box(prio));
}

lean_object * lean_io_map_task_core(lean_object * f, lean_object * t, size_t prio, uint8_t sync) {
    return ::lean_io_map_task(f, t, lean_box(prio), sync);
}

lean_object * lean_io_bind_task_core(lean_object * t, lean_object * f, size_t prio, uint8_t sync) {
    return ::lean_io_bind_task(t, f, lean_box(prio), sync);
}

// ---------------------------------------------------------------------------
// option_ref<object_ref>::get or block
// ---------------------------------------------------------------------------
lean_object * lean_io_option_get_or_block_c(lean_object * o_opt) {
    option_ref<object_ref> opt(o_opt);
    if (opt) {
        return opt.get_val().steal();
    } else {
        lean_panic("PANIC: Promise.result!: promise has been dropped without ever being resolved",
                   /* force_stderr */ true);
        while (true) std::this_thread::sleep_for(std::chrono::seconds::max());
    }
}

// ---------------------------------------------------------------------------
// Windows-only ICU timezone functions (non-Windows returns error)
// ---------------------------------------------------------------------------
lean_object * lean_io_shim_windows_get_next_transition(
        lean_object * tz_str, uint64_t tm_obj, uint8_t default_time) {
#ifdef LEAN_WINDOWS
    return lean_windows_get_next_transition_impl(tz_str, tm_obj, default_time);
#else
    (void)tz_str; (void)tm_obj; (void)default_time;
    return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
        EINVAL, mk_string("failed to get timezone, its windows only.")));
#endif
}

lean_object * lean_io_shim_get_windows_local_timezone_id_at(uint64_t tm) {
#ifdef LEAN_WINDOWS
    return lean_get_windows_local_timezone_id_at_impl(tm);
#else
    (void)tm;
    return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
        EINVAL, mk_string("timezone retrieval is Windows-only")));
#endif
}

#ifdef LEAN_WINDOWS
int lean_io_shim_bcrypt_random(uint8_t * buf, size_t n) {
    NTSTATUS s = BCryptGenRandom(NULL, buf, (ULONG)n, BCRYPT_USE_SYSTEM_PREFERRED_RNG);
    return NT_SUCCESS(s) ? 0 : -1;
}
#endif

} // extern "C"
