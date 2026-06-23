I did not fully fix the bulk over-free. I built the tooling to hunt it, found and characterized it precisely, but could not localize the final missing-increment. The tree is reverted to your committed green state (32/32 harness, builds clean); the only uncommitted change is kernel_bulk_check.sh's all-mode (a more reliable repro). Everything below is documented in memory for a future attempt.

What I built

A deterministic over-free detector in the Rust runtime (poison-on-free + bounded quarantine at the physical-free choke points, a poison-rc check in the inc/dec hot paths, free-site backtrace capture, and per-function thread-local markers). This is the "small pinpoint tool" — it catches the UAF on the first occurrence, no 200k-iteration wait. It's reverted but the rebuild recipe is in memory.

What I found

- Over-free #1: the detector flagged lean_dec(kernel_env) in lean_kernel_check. But the ABI (proven by elab_add_decl_impl) says kernel_env is owned, so removing the dec only leaks it and didn't
fix the crash — debated, reverted.
- Over-free #2 (the dominant one): the victim is a shared tag-0, 3-field structure ([ptr,ptr,bool]), confirmed real and kernel-triggered (env iteration + ci.type access are clean; only
Kernel.check cores). It's freed by the elaborator's normal del_core because it's under-referenced — a missing inc, which has no call-site for the detector to point at.

What I conclusively ruled out (the hunt you directed)

env_find, lean_environment_find (= env.constants.find?'), to_kernel_env, and — decisively — kernel_env.constants rc is never net-changed across a Kernel.check call (0 deltas even in the crashing
full run). The kernel's env handling is balanced; the over-free is not there.

Honest recommendation

Given the kernel env paths are clean and a missing-inc has no site, the two viable paths are (1) an AddressSanitizer build (MI_TRACK_ASAN; partial since this Rust toolchain has no nightly -Zsanitizer), or (2) auditing the shared ported runtime helpers (kernel_expr/kernel_instantiate/kernel_environment/library_elab_environment + SMap/Task ops) for the missing inc on the elab Environment.constants. I'd suggest pausing here rather than burning more effort blind — you flagged rate limits, and I've exhausted the tractable kernel-side leads.

----

# Changes attempted

● Update(src/rust/lean_runtime/src/runtime_object_rc.rs)
  ⎿  Added 13 lines
      551          [const { core::sync::atomic::AtomicU32::new(0) }; QRING_SIZE];
      552      static QHEAD: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);
      553
      554 +    // Free-site backtrace capture for the suspect shape (tag 0, 3 obj fields ~ SMap). On the UAF
      555 +    // we look the object up here and print where its (over-)decrement-to-zero physically freed it.
      556 +    const FB_N: usize = 512;
      557 +    const FB_D: usize = 20;
      558 +    static mut FB_PTR: [usize; FB_N] = [0; FB_N];
      559 +    static mut FB_BT: [[*mut c_void; FB_D]; FB_N] = [[ptr::null_mut(); FB_D]; FB_N];
      560 +    static FB_HEAD: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);
      561 +
      562 +    extern "C" {
      563 +        fn backtrace(buf: *mut *mut c_void, size: i32) -> i32;
      564 +        fn backtrace_symbols_fd(buf: *const *mut c_void, size: i32, fd: i32);
      565 +    }
      566 +
      567      #[inline(always)]
      568      fn qhash(p: usize) -> usize { (p >> 4) & QSET_MASK }
      569

  Read 1 file (ctrl+o to expand)

● Now add the free-site capture in quar_free and the lookup in the report, and remove the now-duplicate local extern:

● Update(src/rust/lean_runtime/src/runtime_object_rc.rs)
  ⎿  Added 9 lines
      626      // Park a block instead of freeing it; evict (and really free) the oldest when the ring wraps.
      627      unsafe fn quar_free(o: *mut LeanObject) {
      628          let p = o as usize;
      629 +        // Capture the free-site backtrace for the suspect shape (tag 0, 3 obj fields ~ SMap), so a
      630 +        // later UAF on it can show exactly where the over-decrement-to-zero happened.
      631 +        if lean_ptr_tag(o) == 0 && (*o).other == 3 {
      632 +            let i = FB_HEAD.fetch_add(1, Ordering::Relaxed) % FB_N;
      633 +            let row = core::ptr::addr_of_mut!(FB_BT[i]) as *mut *mut c_void;
      634 +            for k in 0..FB_D { *row.add(k) = ptr::null_mut(); }
      635 +            backtrace(row, FB_D as i32);
      636 +            *core::ptr::addr_of_mut!(FB_PTR[i]) = p;
      637 +        }
      638          let h = qhash(p);
      639          if QSET[h].load(Ordering::Relaxed) == p {
      640              quar_report(o);

● Update(src/rust/lean_runtime/src/runtime_object_rc.rs)
  ⎿  Added 12 lines
      616              eprintln!(">>> free-site fn: (evicted from ring, unknown)");
      617          }
      618          eprintln!(">>> dangling reference {}-used while executing: {}", op, crate::uaf_fn_name(use_fn));
      620 +        let mut found_bt = false;
      621 +        for i in 0..FB_N {
      622 +            if *core::ptr::addr_of!(FB_PTR[i]) == p {
      623 +                eprintln!(">>> FREE-SITE (over-decrement) backtrace for THIS object:");
      624 +                let row = core::ptr::addr_of!(FB_BT[i]) as *const *mut c_void;
      625 +                backtrace_symbols_fd(row, FB_D as i32, 2);
      626 +                found_bt = true;
      590      // by an over-decrement elsewhere (typically env_find returning a prematurely-freed object).
      591      #[cold]
      592      pub(crate) unsafe fn quar_report_uaf(o: *mut LeanObject, op: &str) {
      593 -        extern "C" {
      594 -            fn backtrace(buf: *mut *mut c_void, size: i32) -> i32;
      595 -            fn backtrace_symbols_fd(buf: *const *mut c_void, size: i32, fd: i32);
      596 -        }
      593          eprintln!("\n=== USE-AFTER-FREE DETECTED ({} of a freed/quarantined object) ===", op);
      594          let tag = lean_ptr_tag(o);
      595          eprintln!("obj={:p} tag={} other(num_objs/elem_sz)={}", o, tag, (*o).other);

● Kernel.Environment.constants is field 0 (so lean_ctor_get(kernel_env, 0) = the SMap). Let me track its refcount across one Kernel.check call — if lean_kernel_check net-decrements it, that's the
  missing inc / extra dec. Let me disable the detector (just track rc) and add a no-alloc tracer:

  Read 1 file (ctrl+o to expand)

● Update(src/rust/lean_runtime/src/kernel_type_checker.rs)
  ⎿  Added 13 lines
      4233  ) -> *mut LeanObject {
      4234      // See lean_kernel_is_def_eq: to_kernel_env CONSUMES env and returns an OWNED kernel env.
      4235      let kernel_env = lean_elab_environment_to_kernel_env(env);
      4236 +    // DEBUG: track the constants SMap (kernel_env field 0) rc across the whole call to find a
      4237 +    // net decrement (missing inc / extra dec) on the shared map.
      4238 +    let smap = lean_ctor_get(kernel_env, 0);
      4239 +    let smap_rc0 = (*smap).rc;
      4240      let mut tc = TypeChecker::new(kernel_env, lctx, DEF_SAFETY_SAFE);
      4241      // The `Kernel.check` debugging API matches C++ `check(expr)` (one arg), which is
      4242      // `check_ignore_undefined_universes` (m_lparams = null). Passing an empty lparam list
     ...
      4249      { let _m = crate::UafFnMark::new(crate::FN_KCHECK_LCTX); lean_dec(lctx); }
      4250      { let _m = crate::UafFnMark::new(crate::FN_KCHECK_A); lean_dec(a); }
      4251      { let _m = crate::UafFnMark::new(crate::FN_TC_DROP); drop(tc); }
      4252 +    let smap_rc1 = (*smap).rc;
      4253 +    if smap_rc0 != smap_rc1 {
      4254 +        extern "C" { fn write(fd: i32, buf: *const u8, n: usize) -> isize; }
      4255 +        let mut b = [0u8; 64]; let mut i = 0usize;
      4256 +        for &c in b"SMAP " { b[i]=c; i+=1; }
      4257 +        let mut wr = |mut v: i64| { if v<0 {b[i]=b'-';i+=1;v=-v;} let mut t=[0u8;12]; let mut tn=0; if v==0 {t[0]=b'0';tn=1;} while v>0 {t[tn]=b'0'+(v%10)as u8;tn+=1;v/=10;} whi
           +le tn>0 {tn-=1;b[i]=t[tn];i+=1;} };
      4258 +        wr(smap_rc0 as i64); b[i]=b' '; i+=1; wr(smap_rc1 as i64); b[i]=b'\n'; i+=1;
      4259 +        write(2, b.as_ptr(), i);
      4260 +    }
      4261      result
      4262  }
      4263

● Bash(cd /home/srghma/projects/lean4
      sed -i 's/pub(crate) const UAF_DETECT: bool = true;/pub(crate) const UAF_DETECT: bool = false;/' src/rust/lean_runtime/src/runtim…)
  ⎿  Running in the background (↓ to manage)

● Bash(f=/tmp/claude-1000/-home-srghma-projects-lean4/d0265d22-692f-4c08-9f3e-13705c0b1532/tasks/ba4fxsfa9.output
      until grep -q 'exit=' "$f" 2>/dev/null; do sleep 12;…)
  ⎿  BUILD=2
     error[E0506]: cannot assign to `b[_]` because it is borrowed
     error[E0503]: cannot use `i` because it was mutably borrowed
     … +4 lines (ctrl+o to expand)

● Background command "Track SMap rc delta across Kernel.check calls" completed (exit code 0)

● Compile error from the closure borrowing. Let me rewrite the tracer without a closure:

● Update(src/rust/lean_runtime/src/kernel_type_checker.rs)
  ⎿  Added 17 lines, removed 6 lines
      4251      { let _m = crate::UafFnMark::new(crate::FN_TC_DROP); drop(tc); }
      4252      let smap_rc1 = (*smap).rc;
      4253      if smap_rc0 != smap_rc1 {
      4257 -        let mut wr = |mut v: i64| { if v<0 {b[i]=b'-';i+=1;v=-v;} let mut t=[0u8;12]; let mut tn=0; if v==0 {t[0]=b'0';tn=1;} while v>0 {t[tn]=b'0'+(v%10)as u8;tn+=1;v/=10;} whi
           -le tn>0 {tn-=1;b[i]=t[tn];i+=1;} };
      4258 -        wr(smap_rc0 as i64); b[i]=b' '; i+=1; wr(smap_rc1 as i64); b[i]=b'\n'; i+=1;
      4259 -        write(2, b.as_ptr(), i);
      4254 +        dbg_smap_rc(smap_rc0 as i64, smap_rc1 as i64);
      4255      }
      4256      result
      4257  }
      4258
      4259 +#[cold]
      4260 +unsafe fn dbg_smap_rc(rc0: i64, rc1: i64) {
      4261 +    extern "C" { fn write(fd: i32, buf: *const u8, n: usize) -> isize; }
      4262 +    fn wr(b: &mut [u8], i: &mut usize, mut v: i64) {
      4263 +        if v < 0 { b[*i] = b'-'; *i += 1; v = -v; }
      4264 +        let mut t = [0u8; 12]; let mut tn = 0;
      4265 +        if v == 0 { t[0] = b'0'; tn = 1; }
      4266 +        while v > 0 { t[tn] = b'0' + (v % 10) as u8; tn += 1; v /= 10; }
      4267 +        while tn > 0 { tn -= 1; b[*i] = t[tn]; *i += 1; }
      4268 +    }
      4269 +    let mut b = [0u8; 64]; let mut i = 0usize;
      4270 +    for &c in b"SMAP " { b[i] = c; i += 1; }
      4271 +    wr(&mut b, &mut i, rc0); b[i] = b' '; i += 1; wr(&mut b, &mut i, rc1); b[i] = b'\n'; i += 1;
      4272 +    write(2, b.as_ptr(), i);
      4273 +}
      4274 +
      4275  /// Build `Except.ok value` (a single-field constructor). `Except` declares `error`
      4276  /// first (tag 0) and `ok` second (tag 1), so `ok` uses tag `EXCEPT_OK_TAG`.
      4277  unsafe fn mk_except_ok(value: *mut LeanObject) -> *mut LeanObject {
