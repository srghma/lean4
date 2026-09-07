import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import process from 'node:process';
import { spawn } from 'node:child_process';

// IO Functions

export function lean_io_timeit(msg, fn) {
  console.time(msg);
  const res = fn();
  console.timeEnd(msg);
  return res;
}

export function lean_io_allocprof(msg, fn) {
  return fn();
}

export function lean_io_initializing() {
  return false;
}

export function lean_io_mono_ms_now() {
  return BigInt(Date.now());
}

export function lean_io_mono_nanos_now() {
  return BigInt(Date.now()) * 1000000n;
}

export function lean_io_get_random_bytes(nBytes) {
  const buf = crypto.randomBytes(Number(nBytes));
  return new Uint8Array(buf);
}

export function lean_io_check_canceled() {
  return false;
}

export function lean_io_cancel(task) {
  return null;
}

export function lean_io_get_task_state(task) {
  return { tag: "TaskState.finished" };
}

export function lean_io_wait(task) {
  return task;
}

export function lean_io_wait_any(tasks) {
  return tasks[0];
}

export function lean_io_get_num_heartbeats() {
  return 0n;
}

export function lean_io_set_heartbeats(count) {
  return null;
}

// Streams

function makeStream(stream) {
  return {
    _1: () => ({ tag: "EST$Out$ok", _1: null }),
    _2: (n) => ({ tag: "EST$Out$ok", _1: new Uint8Array(0) }),
    _3: (arr) => { if (stream) stream.write(Buffer.from(arr)); return { tag: "EST$Out$ok", _1: null }; },
    _4: () => ({ tag: "EST$Out$ok", _1: "" }),
    _5: (s) => { if (stream) stream.write(s); return { tag: "EST$Out$ok", _1: null }; },
    _6: () => stream ? !!stream.isTTY : false
  };
}

let _stdin = makeStream(process.stdin);
let _stdout = makeStream(process.stdout);
let _stderr = makeStream(process.stderr);

export function lean_get_stdin() { return _stdin; }
export function lean_get_stdout() { return _stdout; }
export function lean_get_stderr() { return _stderr; }

export function lean_get_set_stdin(s) { const old = _stdin; _stdin = s; return old; }
export function lean_get_set_stdout(s) { const old = _stdout; _stdout = s; return old; }
export function lean_get_set_stderr(s) { const old = _stderr; _stderr = s; return old; }

// Files

export function lean_io_prim_handle_mk(fn, mode) {
  let flags = 'r';
  switch (mode.tag) {
    case 'read': flags = 'r'; break;
    case 'write': flags = 'w'; break;
    case 'writeNew': flags = 'wx'; break;
    case 'readWrite': flags = 'r+'; break;
    case 'append': flags = 'a'; break;
  }
  const fd = fs.openSync(fn, flags);
  return fd;
}

export function lean_io_prim_handle_lock(h) { return null; }
export function lean_io_prim_handle_try_lock(h) { return true; }
export function lean_io_prim_handle_unlock(h) { return null; }

export function lean_io_prim_handle_is_tty(h) { return false; }
export function lean_io_prim_handle_flush(h) { fs.fsyncSync(h); return null; }
export function lean_io_prim_handle_rewind(h) { return null; }
export function lean_io_prim_handle_truncate(h, size) { fs.ftruncateSync(h, Number(size)); return null; }

export function lean_io_prim_handle_read(h, size) {
  const buf = Buffer.alloc(Number(size));
  const bytesRead = fs.readSync(h, buf, 0, Number(size), null);
  return new Uint8Array(buf.slice(0, bytesRead));
}

export function lean_io_prim_handle_write(h, arr) {
  fs.writeSync(h, Buffer.from(arr));
  return null;
}

export function lean_io_prim_handle_get_line(h) {
  return ""; // Not trivial to implement synchronously without reading byte-by-byte
}

export function lean_io_prim_handle_put_str(h, s) {
  fs.writeSync(h, s);
  return null;
}

// Filesystem

export function lean_io_realpath(p) { return fs.realpathSync(p); }
export function lean_io_remove_file(p) { fs.unlinkSync(p); return null; }
export function lean_io_remove_dir(p) { fs.rmdirSync(p); return null; }
export function lean_io_create_dir(p) { fs.mkdirSync(p); return null; }
export function lean_io_rename(p1, p2) { fs.renameSync(p1, p2); return null; }
export function lean_io_hard_link(p1, p2) { fs.linkSync(p1, p2); return null; }
export function lean_io_create_tempfile() { return "/tmp/lean_tmp_file"; }
export function lean_io_create_tempdir() { return "/tmp/lean_tmp_dir"; }

// Process

export function lean_io_getenv(env) {
  const val = process.env[env];
  return val === undefined ? null : val;
}

export function lean_io_app_path() { return process.argv[1] || ""; }
export function lean_io_current_dir() { return process.cwd(); }

export function lean_io_process_get_current_dir() { return process.cwd(); }
export function lean_io_process_set_current_dir(dir) { process.chdir(dir); return null; }

export function lean_io_process_get_pid() { return BigInt(process.pid); }

export function lean_io_process_spawn(args) {
  // TODO: use spawn
}

export function lean_io_process_child_wait(child) { return 0n; }
export function lean_io_process_child_try_wait(child) { return { tag: "some", _1: 0n }; }
export function lean_io_process_child_kill(child) { return null; }
export function lean_io_process_child_take_stdin(child) { return null; }
export function lean_io_process_child_pid(child) { return 0n; }

export function lean_io_exit(code) { process.exit(Number(code)); }
export function lean_io_force_exit(code) { process.exit(Number(code)); }

export function lean_io_get_tid() { return 0n; }
export function lean_chmod(file, mode) { fs.chmodSync(file, Number(mode)); return null; }

export function lean_io_as_task(...args) {
  throw new Error('not implemented');
}

export function lean_io_map_task(...args) {
  throw new Error('not implemented');
}

export function lean_io_bind_task(...args) {
  throw new Error('not implemented');
}

export function lean_io_read_dir(...args) {
  throw new Error('not implemented');
}

export function lean_io_metadata(...args) {
  throw new Error('not implemented');
}

export function lean_io_symlink_metadata(...args) {
  throw new Error('not implemented');
}

export function lean_runtime_mark_multi_threaded(...args) {
  throw new Error('not implemented');
}

export function lean_runtime_mark_persistent(...args) {
  throw new Error('not implemented');
}

export function lean_runtime_forget(...args) {
  throw new Error('not implemented');
}

export function lean_runtime_hold(...args) {
  throw new Error('not implemented');
}

export const instMonadEIO = () => {
  const pure = (a) => ({ tag: "EST$Out$ok", _1: a });
  const bind = (ma, f) => {
    const res = ma();
    if (res.tag === "EST$Out$ok") return f(res._1)();
    return res;
  };
  // Structure expected by getPure/getBind in Control.js
  return {
    _1: { _1: {}, _2: pure }, // Applicative -> Functor, Pure
    _2: bind // Bind
  };
};
