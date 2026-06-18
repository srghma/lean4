/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Gabriel Ebner, Sebastian Ullrich

.olean serialization and deserialization.
*/
#include <fstream>
#include <sys/stat.h>
#include <cerrno>
#include <cstring>
#include "runtime/interrupt.h"
#include "runtime/sstream.h"
#include "runtime/io.h"
#include "runtime/compact.h"
#include "runtime/option_ref.h"
#include "util/name.h"
#include "library/util.h"
#include "githash.h"

#ifdef LEAN_WINDOWS
#include <windows.h>
#include <io.h>
#include <fcntl.h>
#else
#include <sys/mman.h>
#include <unistd.h>
#include <fcntl.h>
#endif

// `MAP_FIXED_NOREPLACE` turns out to improve mmap hits in the snapshot use case but is exclusive to
// Linux 4.17+ and glibc 2.28+; as this is not a core use case and older kernels will silently
// ignore the flag, we simply define it conditionally.
#if defined(__linux__) && !defined(MAP_FIXED_NOREPLACE)
#define MAP_FIXED_NOREPLACE 0x100000
#endif

#if defined(__has_feature)
#if __has_feature(address_sanitizer)
#include <sanitizer/lsan_interface.h>
#endif
#endif

namespace lean {

namespace {
/** Read up to `n` bytes from `fd` into `buf`, handling `EINTR`. */
ssize_t readn(int fd, void * buf, size_t n) {
    size_t bytes_read_total = 0;
    while (bytes_read_total < n) {
        ssize_t bytes_read = read(fd, static_cast<char*>(buf) + bytes_read_total, n - bytes_read_total);
        if (bytes_read < 0) {
            if (errno == EINTR) continue;
            return -1;
        }
        if (bytes_read == 0) {
            break;
        }
        bytes_read_total += bytes_read;
    }
    return bytes_read_total;
}
}

/** Trivial RAII wrapper for file descriptors so we don't have to worry about `close` management. */
class file_descriptor {
private:
    int m_fd;
public:
    explicit file_descriptor(int fd) : m_fd(fd) {}

    // It should not be copyable
    file_descriptor(const file_descriptor&) = delete;
    file_descriptor& operator=(const file_descriptor&) = delete;

    file_descriptor(file_descriptor&& other) noexcept : m_fd(other.m_fd) {
        other.m_fd = -1;
    }

    ~file_descriptor() {
        if (m_fd != -1) {
            close(m_fd);
        }
    }

    int get() const { return m_fd; }
    operator bool() const { return m_fd != -1; }
};

/** On-disk format of a .olean file. */
struct olean_header {
    // 5 bytes: magic number
    char marker[5] = {'o', 'l', 'e', 'a', 'n'};
    // 1 byte: version, incremented on structural changes to header
    // v2: current `.olean` format
    // v3: new format used for `CompactedRegion.save (allowClosures := true)`; see below for changes
    uint8_t version;
    // 1 byte of flags:
    // * bit 0: whether persisted bignums use GMP or Lean-native encoding
    // * bit 1-7: reserved
    uint8_t flags =
#ifdef LEAN_USE_GMP
        0b1;
#else
        0b0;
#endif
    // 33 bytes: Lean version string, padded with '\0' to the right
    // e.g. "4.12.0-nightly-2024-10-18". Other suffixes after the version
    // triple currently in use are `-rcN` for some `N` and `-pre` for any
    // other non-release commit. Not necessarily null-terminated.
    char lean_version[33];
    // 81b008650766442a0dfa9faa796e4588c9d7d3a1
    // 40 bytes: build githash, padded with `\0` to the right
    char githash[40];
    // address at which the beginning of the file (including header) is attempted to be mmapped
    size_t base_addr;
    // In v3, the fixed header is followed by these length-prefixed sections:
    //   size_t   data_size                                // byte length of the compacted data
    //   compacted data                                    // `data_size` bytes
    //   uint32_t num_closure_offsets
    //   num_closure_offsets × uint64_t                    // data-relative closure `m_fun` offsets
    //   uint32_t num_libs                                 // closure fn-pointer relocation table
    //   num_libs × (size_t base_addr, uint32_t id_len, char id[id_len])  // used libs
    // In v2, the compacted data starts immediately after the header (no `data_size`, no sections).
    size_t data[];
};
// make sure we don't have any padding bytes, which also ensures `data` is properly aligned
static_assert(sizeof(olean_header) == 5 + 1 + 1 + 33 + 40 + sizeof(size_t), "olean_header must be packed");


// Compactor external object: wraps a live `object_compactor` for incremental compaction.
// Keeping the full compactor alive preserves both the `obj_table` (pointer-identity dedup)
// and the `max_sharing_table` (structural dedup) across sequential `lean_compacted_region_save`
// calls so that objects shared between parts are emitted exactly once.

static lean_external_class * g_compactor_class = nullptr;

static void compactor_finalizer(void * data) {
    delete static_cast<object_compactor *>(data);
}

static void compactor_foreach(void *, b_lean_obj_arg) {
    // no Lean object references to trace
}

static void ensure_compactor_class() {
    if (!g_compactor_class) {
        g_compactor_class = lean_register_external_class(compactor_finalizer, compactor_foreach);
    }
}

static lean_object * mk_compactor(void * base_addr, std::vector<compacted_region *> dep_regions,
                                  bool allow_closures) {
    ensure_compactor_class();
    return lean_alloc_external(g_compactor_class,
        new object_compactor(base_addr, std::move(dep_regions), allow_closures));
}

static object_compactor * to_compactor(lean_object * o) {
    return static_cast<object_compactor *>(lean_get_external_data(o));
}

// Extract `compacted_region *` pointers from an `Array CompactedRegion`.
static std::vector<compacted_region *> extract_dep_regions(b_obj_arg odep_regions) {
    std::vector<compacted_region *> result;
    size_t n = lean_array_size(odep_regions);
    result.reserve(n);
    for (size_t i = 0; i < n; i++) {
        result.push_back(reinterpret_cast<compacted_region *>(
            lean_unbox_usize(lean_array_get_core(odep_regions, i))));
    }
    return result;
}

// --- Lib table helpers for closure fn ptr relocation ---

static void write_lib_table(std::ostream & out, std::vector<lib_info> const & libs) {
    uint32_t n = libs.size();
    out.write(reinterpret_cast<char const *>(&n), sizeof(n));
    for (lib_info const & lib : libs) {
        out.write(reinterpret_cast<char const *>(&lib.base_addr), sizeof(lib.base_addr));
        uint32_t len = lib.id.size();
        out.write(reinterpret_cast<char const *>(&len), sizeof(len));
        out.write(lib.id.data(), len);
    }
}

static size_t lib_table_size(std::vector<lib_info> const & libs) {
    size_t sz = sizeof(uint32_t); // num_libs
    for (lib_info const & lib : libs) {
        sz += sizeof(size_t) + sizeof(uint32_t) + lib.id.size();
    }
    return sz;
}


// Parse the closure fn-pointer relocation table from `p` (pointing at `num_libs` in the loaded
// file) into sorted `(saved_base, delta)` pairs. `memcpy` keeps the loads alignment-safe.
static std::vector<std::pair<size_t, ptrdiff_t>> read_lib_table_from_buffer(char const * p) {
    std::vector<std::pair<size_t, ptrdiff_t>> relocs;
    uint32_t n;
    memcpy(&n, p, sizeof(n));
    p += sizeof(n);
    if (n == 0) return relocs;
    std::vector<lib_info> current_libs = get_loaded_libs();
    for (uint32_t i = 0; i < n; i++) {
        size_t old_base;
        memcpy(&old_base, p, sizeof(old_base));
        p += sizeof(old_base);
        uint32_t len;
        memcpy(&len, p, sizeof(len));
        p += sizeof(len);
        std::string id(p, len);
        p += len;
        size_t new_base = 0;
        bool found = false;
        for (lib_info const & lib : current_libs) {
            if (lib.id == id) {
                new_base = lib.base_addr;
                found = true;
                break;
            }
        }
        if (!found)
            throw exception((sstream() << "library required for closure relocation is not loaded "
                                          "in this process: '" << id << "'").str());
        ptrdiff_t delta = static_cast<ptrdiff_t>(new_base) - static_cast<ptrdiff_t>(old_base);
        relocs.push_back({old_base, delta});
    }
    std::sort(relocs.begin(), relocs.end());
    return relocs;
}

extern "C" LEAN_EXPORT object * lean_cxx_compacted_region_save(b_obj_arg ofname, b_obj_arg mod, b_obj_arg odata,
                                                           b_obj_arg odep_regions, obj_arg oprev,
                                                           uint8 allow_closures_u8, object *) {
    // `mmap` addresses must be page-aligned. The default (non-huge) page size on x86-64 is 4KB;
    // `MapViewOfFileEx` addresses must be aligned to the "memory allocation granularity" (64KB).
    const size_t ALIGN = 1LL<<16;
    bool allow_closures = allow_closures_u8 != 0;

    option_ref<object_ref> prev(oprev);
    object_ref cs_obj;
    if (prev) {
        cs_obj = prev.get_val();
    } else {
        // Derive a base address that is uniformly distributed but deterministic, and should most
        // likely work for `mmap` on all interesting platforms.
        // NOTE: an overlapping/non-compatible base address does not prevent the module from being
        // imported, merely from using `mmap` for that.
        // Start with a hash of the module name. While our string hash is a dubious 32-bit
        // algorithm, the mixing of multiple `Name` parts seems to result in a nicely distributed
        // 64-bit output.
        size_t base_addr = name(mod, true).hash();
        // x86-64 user space is currently limited to the lower 47 bits
        // (https://en.wikipedia.org/wiki/X86-64#Virtual_address_space_details).
        // On Linux at least, the stack grows down from ~0x7fff... followed by shared libraries,
        // so reserve a bit of space for them (0x7fff...-0x7f00... = 1TB).
        base_addr = base_addr % 0x7f0000000000;
        base_addr = base_addr & ~(ALIGN - 1);
        std::vector<compacted_region *> dep_regions = extract_dep_regions(odep_regions);
        cs_obj = object_ref(mk_compactor(reinterpret_cast<void *>(base_addr),
                                         std::move(dep_regions), allow_closures));
    }

    object_compactor & compactor = *to_compactor(cs_obj.raw());

    char const * olean_fn = lean_string_cstr(ofname);
    // We first write to a temp file and then move it to the correct path (possibly deleting an
    // older file) so that we neither expose partially-written files nor modify possibly
    // memory-mapped files.
#ifdef LEAN_WINDOWS
    uint32_t pid = GetCurrentProcessId();
#else
    uint32_t pid = getpid();
#endif
    std::string olean_tmp_fn = std::string(olean_fn) + ".tmp." + std::to_string(pid);

    try {
        std::ofstream out(olean_tmp_fn, std::ios_base::binary);

        if (!allow_closures) {
            // v2 path: just `[header][data]`, no extension, no trailer.
            // Compactor errors on closures.
            if (compactor.size() % ALIGN != 0) {
                compactor.alloc(ALIGN - (compactor.size() % ALIGN));
            }
            size_t file_offset = compactor.size();
            // Reserve space in the compactor buffer for the header so subsequent objects'
            // `base_addr`-relative offsets land in the right spot. The header is written directly
            // to `out` below; these reserved bytes are never read back.
            compactor.alloc(sizeof(olean_header));
            olean_header header = {};
            header.version = 2;
            header.base_addr = reinterpret_cast<size_t>(compactor.base_addr()) + file_offset;
            strncpy(header.lean_version, get_short_version_string().c_str(), sizeof(header.lean_version));
            strncpy(header.githash, LEAN_GITHASH, sizeof(header.githash));
            out.write(reinterpret_cast<char *>(&header), sizeof(header));

            compactor(odata);

            if (out.fail()) {
                throw exception((sstream() << "failed to create file '" << olean_fn << "'").str());
            }
            out.write(static_cast<char const *>(compactor.data()) + file_offset + sizeof(olean_header),
                      compactor.size() - file_offset - sizeof(olean_header));
            out.close();
        } else {
            // v3 format
            // NOTE: each section's data MUST be reserved in the compactor buffer, even when
            // trailing the actual compactor data, so that any follow-up compaction stays in sync
            // instead of attempting to map on top of the trailing data
            if (compactor.size() % ALIGN != 0) {
                compactor.alloc(ALIGN - (compactor.size() % ALIGN));
            }
            size_t file_offset = compactor.size();

            compactor.alloc(sizeof(olean_header));
            olean_header header = {};
            header.version = 3;
            header.base_addr = reinterpret_cast<size_t>(compactor.base_addr()) + file_offset;
            strncpy(header.lean_version, get_short_version_string().c_str(), sizeof(header.lean_version));
            strncpy(header.githash, LEAN_GITHASH, sizeof(header.githash));
            out.write(reinterpret_cast<char *>(&header), sizeof(header));

            // `data_size`: reserve its slot now so the data lands at the right buffer offset (and
            // stays `size_t`-aligned: 88 + 8 = 96); its value is only known once the data is
            // serialized, so it is written just below.
            compactor.alloc(sizeof(size_t));

            compactor(odata);

            size_t data_offset = file_offset + sizeof(olean_header) + sizeof(size_t);
            size_t data_size = compactor.size() - data_offset;
            out.write(reinterpret_cast<char const *>(&data_size), sizeof(data_size));
            out.write(static_cast<char const *>(compactor.data()) + data_offset, data_size);

            // Read everything we need from the compactor buffer now: the trailer `alloc`s below
            // may reallocate it. `used_libs()` maps each recorded closure fn pointer to its
            // library; only those libraries are written. `file_offsets` are this part's closure
            // `m_fun` offsets made data-section-relative.
            std::vector<lib_info> used_libs = compactor.used_libs();
            std::vector<size_t> & all_offsets = compactor.closure_offsets();
            std::vector<uint64_t> file_offsets;
            for (size_t off : all_offsets) {
                file_offsets.push_back(static_cast<uint64_t>(off - data_offset));
            }
            // Clear so a chained next part accumulates only its own closures.
            all_offsets.clear();

            // Closure section.
            uint32_t num_closure_offsets = static_cast<uint32_t>(file_offsets.size());
            compactor.alloc(sizeof(num_closure_offsets));
            out.write(reinterpret_cast<char const *>(&num_closure_offsets), sizeof(num_closure_offsets));
            if (!file_offsets.empty()) {
                compactor.alloc(file_offsets.size() * sizeof(uint64_t));
                out.write(reinterpret_cast<char const *>(file_offsets.data()),
                          file_offsets.size() * sizeof(uint64_t));
            }

            // Relocation table: only the libraries containing a compacted closure's fn pointer.
            compactor.alloc(lib_table_size(used_libs));
            write_lib_table(out, used_libs);

            if (out.fail()) {
                throw exception((sstream() << "failed to create file '" << olean_fn << "'").str());
            }
            out.close();
        }
    } catch (exception & ex) {
        std::remove(olean_tmp_fn.c_str());
        return io_result_mk_error((sstream() << "failed to write '" << olean_fn << "': " << ex.what()).str());
    }

    // Atomic rename
    while (std::rename(olean_tmp_fn.c_str(), olean_fn) != 0) {
#ifdef LEAN_WINDOWS
        if (errno == EEXIST) {
            // Memory-mapped files can be deleted starting with Windows 10 using "POSIX semantics".
            HANDLE h_olean_fn = CreateFile(olean_fn, GENERIC_READ | DELETE, FILE_SHARE_READ | FILE_SHARE_DELETE, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
            if (h_olean_fn == INVALID_HANDLE_VALUE) {
                return io_result_mk_error((sstream() << "failed to open '" << olean_fn << "': " << GetLastError()).str());
            }
            FILE_DISPOSITION_INFO_EX fdi = { FILE_DISPOSITION_FLAG_DELETE | FILE_DISPOSITION_FLAG_POSIX_SEMANTICS };
            if (SetFileInformationByHandle(h_olean_fn, static_cast<FILE_INFO_BY_HANDLE_CLASS>(21) /* FileDispositionInfoEx */, &fdi, sizeof(fdi)) != 0) {
                lean_always_assert(CloseHandle(h_olean_fn));
                continue;
            } else {
                return io_result_mk_error((sstream() << "failed to delete '" << olean_fn << "': " << GetLastError()).str());
            }
        }
#endif
        return io_result_mk_error((sstream() << "failed to write '" << olean_fn << "': " << errno << " " << strerror(errno)).str());
    }

    return io_result_mk_ok(cs_obj.steal());
}


}
