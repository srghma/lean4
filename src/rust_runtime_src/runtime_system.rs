/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(all(feature = "std", not(target_family = "wasm")))]
mod runtime_system_impl {
    use super::*;
    use core::mem::MaybeUninit;
    use core::ptr::{addr_of, addr_of_mut, null_mut};

    const PATH_MAX: usize = 4096;
    const INET_ADDRSTRLEN: usize = 16;
    const INET6_ADDRSTRLEN: usize = 46;

    const UV_ENOENT: c_int = -2;
    const UV_ENOBUFS: c_int = -105;

    #[repr(C)]
    struct UvCpuTimes {
        user: u64,
        nice: u64,
        sys: u64,
        idle: u64,
        irq: u64,
    }

    #[repr(C)]
    struct UvCpuInfo {
        model: *mut c_char,
        speed: c_int,
        _padding: c_int,
        cpu_times: UvCpuTimes,
    }

    #[repr(C)]
    struct UvPasswd {
        username: *mut c_char,
        uid: c_long,
        gid: c_long,
        shell: *mut c_char,
        homedir: *mut c_char,
    }

    #[repr(C)]
    struct UvGroup {
        groupname: *mut c_char,
        gid: c_long,
        members: *mut *mut c_char,
    }

    #[repr(C)]
    struct UvEnvItem {
        name: *mut c_char,
        value: *mut c_char,
    }

    #[repr(C)]
    struct UvUtsname {
        sysname: [c_char; 256],
        release: [c_char; 256],
        version: [c_char; 256],
        machine: [c_char; 256],
    }

    #[repr(C)]
    struct UvTimeval {
        tv_sec: c_long,
        tv_usec: c_long,
    }

    #[repr(C)]
    struct UvRusage {
        ru_utime: UvTimeval,
        ru_stime: UvTimeval,
        ru_maxrss: u64,
        ru_ixrss: u64,
        ru_idrss: u64,
        ru_isrss: u64,
        ru_minflt: u64,
        ru_majflt: u64,
        ru_nswap: u64,
        ru_inblock: u64,
        ru_oublock: u64,
        ru_msgsnd: u64,
        ru_msgrcv: u64,
        ru_nsignals: u64,
        ru_nvcsw: u64,
        ru_nivcsw: u64,
    }

    #[repr(C, align(8))]
    struct UvRandom {
        storage: [u8; 144],
    }

    #[repr(C)]
    struct RandomReq {
        req: UvRandom,
        promise: *mut LeanObject,
        byte_array: *mut LeanObject,
    }

    extern "C" {
        fn uv_get_process_title(buffer: *mut c_char, size: usize) -> c_int;
        fn uv_set_process_title(title: *const c_char) -> c_int;
        fn uv_uptime(uptime: *mut f64) -> c_int;
        fn uv_os_getpid() -> u32;
        fn uv_os_getppid() -> u32;
        fn uv_cpu_info(info: *mut *mut UvCpuInfo, count: *mut c_int) -> c_int;
        fn uv_free_cpu_info(info: *mut UvCpuInfo, count: c_int);
        fn uv_cwd(buffer: *mut c_char, size: *mut usize) -> c_int;
        fn uv_chdir(dir: *const c_char) -> c_int;
        fn uv_os_homedir(buffer: *mut c_char, size: *mut usize) -> c_int;
        fn uv_os_tmpdir(buffer: *mut c_char, size: *mut usize) -> c_int;
        fn uv_os_get_passwd(pwd: *mut UvPasswd) -> c_int;
        fn uv_os_free_passwd(pwd: *mut UvPasswd);
        fn uv_os_get_group(grp: *mut UvGroup, gid: u64) -> c_int;
        fn uv_os_free_group(grp: *mut UvGroup);
        fn uv_os_environ(env: *mut *mut UvEnvItem, count: *mut c_int) -> c_int;
        fn uv_os_free_environ(env: *mut UvEnvItem, count: c_int);
        fn uv_os_getenv(name: *const c_char, buffer: *mut c_char, size: *mut usize) -> c_int;
        fn uv_os_setenv(name: *const c_char, value: *const c_char) -> c_int;
        fn uv_os_unsetenv(name: *const c_char) -> c_int;
        fn uv_os_gethostname(buffer: *mut c_char, size: *mut usize) -> c_int;
        fn uv_os_getpriority(pid: u32, priority: *mut c_int) -> c_int;
        fn uv_os_setpriority(pid: u32, priority: c_int) -> c_int;
        fn uv_os_uname(uts: *mut UvUtsname) -> c_int;
        fn uv_hrtime() -> u64;
        fn uv_random(
            loop_: *mut UvLoop,
            req: *mut UvRandom,
            buf: *mut c_void,
            buflen: usize,
            flags: c_uint,
            cb: Option<unsafe extern "C" fn(*mut UvRandom, c_int, *mut c_void, usize)>,
        ) -> c_int;
        fn uv_getrusage(usage: *mut UvRusage) -> c_int;
        fn uv_exepath(buffer: *mut c_char, size: *mut usize) -> c_int;
        fn uv_get_free_memory() -> u64;
        fn uv_get_total_memory() -> u64;
        fn uv_get_constrained_memory() -> u64;
        fn uv_get_available_memory() -> u64;
        fn uv_strerror(err: c_int) -> *const c_char;

    }

    unsafe fn option_none() -> *mut LeanObject {
        lean_box(0)
    }

    unsafe fn option_some(value: *mut LeanObject) -> *mut LeanObject {
        let result = lean_runtime_alloc_ctor(1, 1, 0);
        lean_runtime_ctor_set(result, 0, value);
        result
    }

    unsafe fn mk_except_ok(value: *mut LeanObject) -> *mut LeanObject {
        let result = lean_runtime_alloc_ctor(1, 1, 0);
        lean_runtime_ctor_set(result, 0, value);
        result
    }

    unsafe fn mk_except_err(error: *mut LeanObject) -> *mut LeanObject {
        let result = lean_runtime_alloc_ctor(0, 1, 0);
        lean_runtime_ctor_set(result, 0, error);
        result
    }

    unsafe fn lean_array_set(obj: *mut LeanObject, idx: usize, value: *mut LeanObject) {
        let array_data_ptr = (obj as *mut u8).add(24) as *mut *mut LeanObject;
        array_data_ptr.add(idx).write(value);
    }

    unsafe fn timeval_to_millis(t: UvTimeval) -> u64 {
        (t.tv_sec as u64) * 1000 + (t.tv_usec as u64) / 1000
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_get_process_title() -> *mut LeanObject {
        let mut title = [0 as c_char; 512];
        let result = uv_get_process_title(title.as_mut_ptr(), title.len());

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        let lean_title = lean_mk_string(title.as_ptr());
        lean_io_result_mk_ok(lean_title)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_set_process_title(title: *mut LeanObject) -> *mut LeanObject {
        let title_str = lean_string_cstr(title);
        let len = libc::strlen(title_str);
        if len != lean_string_size(title) - 1 {
            return mk_embedded_nul_error(title);
        }
        let result = uv_set_process_title(title_str);

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box(0))
    }

    extern "C" {
        fn printf(format: *const c_char, ...) -> c_int;
        fn fflush(stream: *mut c_void) -> c_int;
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_uptime() -> *mut LeanObject {
        printf(c"lean_uv_uptime entry\n".as_ptr());
        fflush(null_mut());
        let mut uptime = 0.0;
        let result = uv_uptime(&mut uptime);
        printf(
            c"uv_uptime result = %d, uptime = %f\n".as_ptr(),
            result,
            uptime,
        );
        fflush(null_mut());

        if result < 0 {
            printf(c"uv_uptime error\n".as_ptr());
            fflush(null_mut());
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        let lean_uptime = lean_box_uint64(uptime as u64);
        printf(c"lean_uptime = %p\n".as_ptr(), lean_uptime);
        fflush(null_mut());
        let res = lean_io_result_mk_ok(lean_uptime);
        printf(c"lean_io_result_mk_ok = %p\n".as_ptr(), res);
        fflush(null_mut());
        res
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_os_getpid() -> *mut LeanObject {
        let pid = uv_os_getpid();
        lean_io_result_mk_ok(lean_box_uint64(pid as u64))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_os_getppid() -> *mut LeanObject {
        let ppid = uv_os_getppid();
        lean_io_result_mk_ok(lean_box_uint64(ppid as u64))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_cpu_info() -> *mut LeanObject {
        let mut cpu_infos = null_mut();
        let mut count = 0;
        let result = uv_cpu_info(&mut cpu_infos, &mut count);

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        let count_usize = count as usize;
        let lean_cpu_infos = lean_alloc_array(count_usize, count_usize);

        for i in 0..count_usize {
            let cpu_info_ptr = &*cpu_infos.add(i);
            let times = lean_runtime_alloc_ctor(0, 0, 40);
            lean_ctor_set_uint64(times, 0, cpu_info_ptr.cpu_times.user);
            lean_ctor_set_uint64(times, 8, cpu_info_ptr.cpu_times.nice);
            lean_ctor_set_uint64(times, 16, cpu_info_ptr.cpu_times.sys);
            lean_ctor_set_uint64(times, 24, cpu_info_ptr.cpu_times.idle);
            lean_ctor_set_uint64(times, 32, cpu_info_ptr.cpu_times.irq);

            let model = lean_mk_string(cpu_info_ptr.model);

            let cpu_info = lean_runtime_alloc_ctor(0, 2, 8);
            lean_runtime_ctor_set(cpu_info, 0, model);
            lean_runtime_ctor_set(cpu_info, 1, times);
            lean_ctor_set_uint64(
                cpu_info,
                core::mem::size_of::<*mut c_void>() * 2,
                cpu_info_ptr.speed as u64,
            );

            lean_array_set(lean_cpu_infos, i, cpu_info);
        }

        uv_free_cpu_info(cpu_infos, count);
        lean_io_result_mk_ok(lean_cpu_infos)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_cwd() -> *mut LeanObject {
        let mut buffer = [0 as c_char; PATH_MAX];
        let mut size = buffer.len();
        let result = uv_cwd(buffer.as_mut_ptr(), &mut size);

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        let lean_cwd = lean_mk_string(buffer.as_ptr());
        lean_io_result_mk_ok(lean_cwd)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_chdir(path: *mut LeanObject) -> *mut LeanObject {
        let path_str = lean_string_cstr(path);
        let len = libc::strlen(path_str);
        if len != lean_string_size(path) - 1 {
            return mk_embedded_nul_error(path);
        }

        let result = uv_chdir(path_str);

        if result < 0 {
            lean_inc(path);
            return lean_io_result_mk_error(lean_decode_uv_error(result, path));
        }

        lean_io_result_mk_ok(lean_box(0))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_os_homedir() -> *mut LeanObject {
        let mut buffer = [0 as c_char; PATH_MAX];
        let mut size = buffer.len();
        let result = uv_os_homedir(buffer.as_mut_ptr(), &mut size);

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        let lean_homedir = lean_mk_string(buffer.as_ptr());
        lean_io_result_mk_ok(lean_homedir)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_os_tmpdir() -> *mut LeanObject {
        let mut buffer = [0 as c_char; PATH_MAX];
        let mut size = buffer.len();
        let result = uv_os_tmpdir(buffer.as_mut_ptr(), &mut size);

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        let lean_tmpdir = lean_mk_string(buffer.as_ptr());
        lean_io_result_mk_ok(lean_tmpdir)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_os_get_passwd() -> *mut LeanObject {
        let mut passwd = MaybeUninit::<UvPasswd>::uninit();
        let result = uv_os_get_passwd(passwd.as_mut_ptr());

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        let passwd = passwd.assume_init();
        let username = lean_mk_string(passwd.username);
        let uid = if passwd.uid != -1 {
            option_some(lean_box_uint64(passwd.uid as u64))
        } else {
            option_none()
        };
        let gid = if passwd.gid != -1 {
            option_some(lean_box_uint64(passwd.gid as u64))
        } else {
            option_none()
        };
        let shell = if !passwd.shell.is_null() {
            option_some(lean_mk_string(passwd.shell))
        } else {
            option_none()
        };
        let homedir = if !passwd.homedir.is_null() {
            option_some(lean_mk_string(passwd.homedir))
        } else {
            option_none()
        };

        let passwd_info = lean_runtime_alloc_ctor(0, 5, 0);
        lean_runtime_ctor_set(passwd_info, 0, username);
        lean_runtime_ctor_set(passwd_info, 1, uid);
        lean_runtime_ctor_set(passwd_info, 2, gid);
        lean_runtime_ctor_set(passwd_info, 3, shell);
        lean_runtime_ctor_set(passwd_info, 4, homedir);

        uv_os_free_passwd(addr_of!(passwd).cast_mut());

        lean_io_result_mk_ok(passwd_info)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_os_get_group(gid: u64) -> *mut LeanObject {
        let mut group = MaybeUninit::<UvGroup>::uninit();
        let result = uv_os_get_group(group.as_mut_ptr(), gid);

        if result == UV_ENOENT {
            return lean_io_result_mk_ok(option_none());
        }

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(
                result,
                lean_mk_string(b"group\0".as_ptr().cast()),
            ));
        }

        let group = group.assume_init();
        let groupname = lean_mk_string(group.groupname);

        let mut count = 0;
        let mut mem_ptr = group.members;
        while !mem_ptr.is_null() && !(*mem_ptr).is_null() {
            count += 1;
            mem_ptr = mem_ptr.add(1);
        }

        let mut members = lean_mk_empty_array();
        for i in 0..count {
            let member_name = lean_mk_string(*group.members.add(i));
            members = lean_array_push(members, member_name);
        }

        let group_info = lean_runtime_alloc_ctor(0, 2, 8);
        lean_runtime_ctor_set(group_info, 0, groupname);
        lean_runtime_ctor_set(group_info, 1, members);
        lean_ctor_set_uint64(
            group_info,
            core::mem::size_of::<*mut c_void>() * 2,
            group.gid as u64,
        );

        uv_os_free_group(addr_of!(group).cast_mut());

        lean_io_result_mk_ok(option_some(group_info))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_os_environ() -> *mut LeanObject {
        let mut env = null_mut();
        let mut count = 0;
        let result = uv_os_environ(&mut env, &mut count);

        if result < 0 {
            return lean_io_result_mk_error(lean_mk_string(
                CStr::from_ptr(uv_strerror(result)).as_ptr(),
            ));
        }

        let mut env_array = lean_mk_empty_array();

        for i in 0..count as usize {
            let item = env.add(i);
            let name = lean_mk_string((*item).name);
            let value = lean_mk_string((*item).value);

            let pair = lean_runtime_alloc_ctor(0, 2, 0);
            lean_runtime_ctor_set(pair, 0, name);
            lean_runtime_ctor_set(pair, 1, value);

            env_array = lean_array_push(env_array, pair);
        }

        uv_os_free_environ(env, count);

        lean_io_result_mk_ok(env_array)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_os_getenv(name: *mut LeanObject) -> *mut LeanObject {
        let name_str = lean_string_cstr(name);
        let len = libc::strlen(name_str);
        if len != lean_string_size(name) - 1 {
            return lean_io_result_mk_ok(option_none());
        }

        let mut stack_buffer = [0 as c_char; 1024];
        let mut size = stack_buffer.len();

        let mut result = uv_os_getenv(name_str, stack_buffer.as_mut_ptr(), &mut size);

        if result == UV_ENOENT {
            return lean_io_result_mk_ok(option_none());
        } else if result == UV_ENOBUFS {
            let heap_buffer = libc::malloc(size).cast::<c_char>();
            if heap_buffer.is_null() {
                return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
            }

            result = uv_os_getenv(name_str, heap_buffer, &mut size);

            if result == UV_ENOENT {
                libc::free(heap_buffer.cast());
                return lean_io_result_mk_ok(option_none());
            } else if result < 0 {
                libc::free(heap_buffer.cast());
                return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
            }

            let value = lean_mk_string(heap_buffer);
            let some_value = option_some(value);
            libc::free(heap_buffer.cast());
            return lean_io_result_mk_ok(some_value);
        } else if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        let value = lean_mk_string(stack_buffer.as_ptr());
        let some_value = option_some(value);
        lean_io_result_mk_ok(some_value)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_os_setenv(
        name: *mut LeanObject,
        value: *mut LeanObject,
    ) -> *mut LeanObject {
        let name_str = lean_string_cstr(name);
        let value_str = lean_string_cstr(value);
        if libc::strlen(name_str) != lean_string_size(name) - 1 {
            return mk_embedded_nul_error(name);
        }
        if libc::strlen(value_str) != lean_string_size(value) - 1 {
            return mk_embedded_nul_error(value);
        }

        let result = uv_os_setenv(name_str, value_str);

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box(0))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_os_unsetenv(name: *mut LeanObject) -> *mut LeanObject {
        let name_str = lean_string_cstr(name);
        if libc::strlen(name_str) != lean_string_size(name) - 1 {
            return mk_embedded_nul_error(name);
        }

        let result = uv_os_unsetenv(name_str);

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box(0))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_os_gethostname() -> *mut LeanObject {
        let mut hostname = [0 as c_char; 256];
        let mut size = hostname.len();

        let result = uv_os_gethostname(hostname.as_mut_ptr(), &mut size);

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        let lean_hostname = lean_mk_string(hostname.as_ptr());
        lean_io_result_mk_ok(lean_hostname)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_os_getpriority(pid: u64) -> *mut LeanObject {
        let mut priority = 0;
        let result = uv_os_getpriority(pid as u32, &mut priority);

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box_uint64(priority as u64))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_os_setpriority(pid: u64, priority: i64) -> *mut LeanObject {
        let result = uv_os_setpriority(pid as u32, priority as c_int);

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box(0))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_os_uname() -> *mut LeanObject {
        let mut uname_info = MaybeUninit::<UvUtsname>::uninit();
        let result = uv_os_uname(uname_info.as_mut_ptr());

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        let uname_info = uname_info.assume_init();
        let sysname = lean_mk_string(uname_info.sysname.as_ptr());
        let release = lean_mk_string(uname_info.release.as_ptr());
        let version = lean_mk_string(uname_info.version.as_ptr());
        let machine = lean_mk_string(uname_info.machine.as_ptr());

        let uname = lean_runtime_alloc_ctor(0, 4, 0);
        lean_runtime_ctor_set(uname, 0, sysname);
        lean_runtime_ctor_set(uname, 1, release);
        lean_runtime_ctor_set(uname, 2, version);
        lean_runtime_ctor_set(uname, 3, machine);

        lean_io_result_mk_ok(uname)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_hrtime() -> *mut LeanObject {
        let time = uv_hrtime();
        lean_io_result_mk_ok(lean_box_uint64(time))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_random(size: u64) -> *mut LeanObject {
        let req = libc::malloc(core::mem::size_of::<RandomReq>()).cast::<RandomReq>();
        if req.is_null() {
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        let promise = lean_io_promise_new();
        lean_mark_mt(promise);
        (*req).promise = promise;

        let byte_array = lean_alloc_sarray(1, 0, size as usize);
        (*req).byte_array = byte_array;

        (*req).req.storage = [0; 144];
        let req_data_ptr = addr_of_mut!((*req).req).cast::<UvHandle>();
        (*req_data_ptr).data = req.cast();

        lean_inc(promise);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        unsafe extern "C" fn random_cb(
            uv_req: *mut UvRandom,
            status: c_int,
            _buf: *mut c_void,
            buflen: usize,
        ) {
            let handle = uv_req.cast::<UvHandle>();
            let req = (*handle).data.cast::<RandomReq>();

            if status < 0 {
                lean_dec((*req).byte_array);
                let result = lean_io_promise_resolve(
                    mk_except_err(lean_decode_uv_error(status, null_mut())),
                    (*req).promise,
                );
                lean_dec(result);
            } else {
                lean_sarray_set_size((*req).byte_array, buflen);
                let result =
                    lean_io_promise_resolve(mk_except_ok((*req).byte_array), (*req).promise);
                lean_dec(result);
            }

            lean_dec((*req).promise);
            libc::free(req.cast());
        }

        let result = uv_random(
            _ZN4lean9global_evE.loop_,
            addr_of_mut!((*req).req),
            lean_sarray_cptr(byte_array).cast_mut().cast(),
            size as usize,
            0,
            Some(random_cb),
        );

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            lean_dec(byte_array);
            lean_dec(promise);
            lean_dec(promise);
            libc::free(req.cast());

            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(promise)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_getrusage() -> *mut LeanObject {
        let mut usage = MaybeUninit::<UvRusage>::uninit();
        let result = uv_getrusage(usage.as_mut_ptr());

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        let usage = usage.assume_init();
        let r = lean_runtime_alloc_ctor(0, 0, 128);
        lean_ctor_set_uint64(r, 0, timeval_to_millis(usage.ru_utime));
        lean_ctor_set_uint64(r, 8, timeval_to_millis(usage.ru_stime));
        lean_ctor_set_uint64(r, 16, usage.ru_maxrss);
        lean_ctor_set_uint64(r, 24, usage.ru_ixrss);
        lean_ctor_set_uint64(r, 32, usage.ru_idrss);
        lean_ctor_set_uint64(r, 40, usage.ru_isrss);
        lean_ctor_set_uint64(r, 48, usage.ru_minflt);
        lean_ctor_set_uint64(r, 56, usage.ru_majflt);
        lean_ctor_set_uint64(r, 64, usage.ru_nswap);
        lean_ctor_set_uint64(r, 72, usage.ru_inblock);
        lean_ctor_set_uint64(r, 80, usage.ru_oublock);
        lean_ctor_set_uint64(r, 88, usage.ru_msgsnd);
        lean_ctor_set_uint64(r, 96, usage.ru_msgrcv);
        lean_ctor_set_uint64(r, 104, usage.ru_nsignals);
        lean_ctor_set_uint64(r, 112, usage.ru_nvcsw);
        lean_ctor_set_uint64(r, 120, usage.ru_nivcsw);

        lean_io_result_mk_ok(r)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_exepath() -> *mut LeanObject {
        let mut buffer = [0 as c_char; PATH_MAX];
        let mut size = buffer.len();
        let result = uv_exepath(buffer.as_mut_ptr(), &mut size);

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        let path = lean_mk_string(buffer.as_ptr());
        lean_io_result_mk_ok(path)
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_get_free_memory() -> *mut LeanObject {
        let mem = uv_get_free_memory();
        lean_io_result_mk_ok(lean_box_uint64(mem))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_get_total_memory() -> *mut LeanObject {
        let mem = uv_get_total_memory();
        lean_io_result_mk_ok(lean_box_uint64(mem))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_get_constrained_memory() -> *mut LeanObject {
        let mem = uv_get_constrained_memory();
        lean_io_result_mk_ok(lean_box_uint64(mem))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_get_available_memory() -> *mut LeanObject {
        let mem = uv_get_available_memory();
        lean_io_result_mk_ok(lean_box_uint64(mem))
    }
}

#[cfg(all(feature = "std", not(target_family = "wasm")))]
pub use runtime_system_impl::*;

#[cfg(all(feature = "std", target_family = "wasm"))]
mod runtime_system_impl {
    use super::*;

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_get_process_title() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_set_process_title(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_uptime() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_os_getpid() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_os_getppid() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_cpu_info() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_cwd() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_chdir(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_os_homedir() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_os_tmpdir() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_os_get_passwd() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_os_get_group(_: u64) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_os_environ() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_os_getenv(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_os_setenv(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_os_unsetenv(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_os_gethostname() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_os_getpriority(_: u64) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_os_setpriority(_: u64, _: i64) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_os_uname() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_hrtime() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_random(_: u64) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_getrusage() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_exepath() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_get_free_memory() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_get_total_memory() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_get_constrained_memory() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub extern "C" fn lean_uv_get_available_memory() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
}

#[cfg(all(feature = "std", target_family = "wasm"))]
pub use runtime_system_impl::*;
