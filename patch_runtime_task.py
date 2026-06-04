#!/usr/bin/env python3
"""
patch_runtime_task.py  —  Fix the hardest errors in runtime_task.rs
Run from the lean4 repo root:
  python3 patch_runtime_task.py src/rust/lean_runtime/src/runtime_task.rs
"""

import sys, re, textwrap

if len(sys.argv) < 2:
    print("Usage: python3 patch_runtime_task.py <path/to/runtime_task.rs>")
    sys.exit(1)

path = sys.argv[1]
with open(path) as f:
    src = f.read()

original = src

# ─────────────────────────────────────────────────────────────────────────────
# 1. Remove duplicate use declarations that are already in lib.rs crate root
# ─────────────────────────────────────────────────────────────────────────────
for pattern in [
    r'^use super::\*;\n',
    r'^use core::sync::atomic::Ordering;\n',
]:
    src = re.sub(pattern, '', src, flags=re.MULTILINE)

# ─────────────────────────────────────────────────────────────────────────────
# 2. Remove duplicate const declarations (already in runtime_object_rc.rs)
# ─────────────────────────────────────────────────────────────────────────────
# Remove the first occurrence of LEAN_TASK_TAG and LEAN_PROMISE_TAG
for const_name in ['LEAN_TASK_TAG', 'LEAN_PROMISE_TAG']:
    src = re.sub(
        rf'^const {const_name}: u8 = \d+;\n',
        '',
        src,
        count=1,
        flags=re.MULTILINE
    )

# ─────────────────────────────────────────────────────────────────────────────
# 3. Remove duplicate extern fn declarations
#    (already defined in lib.rs or other Rust files)
# ─────────────────────────────────────────────────────────────────────────────
dups = [
    "lean_free_small_object",
    "lean_closure_arg_cptr",
    "lean_inc_ref",
    "lean_dec_ref",
    "lean_task_get",
    "lean_io_get_task_state_core",
    "lean_io_promise_new",
    "lean_io_promise_resolve",
    "lean_promise_resolve",
    "deactivate_task",
    "deactivate_promise",
    "lean_mark_mt",
    "lean_io_check_canceled_core",
    "lean_io_cancel_core",
    "lean_io_wait_any_core",
    "save_stack_info",
    "reset_heartbeat",
]
for sym in dups:
    src = re.sub(
        rf'^[^\S\n]*fn {re.escape(sym)}\([^;]*\)(?:\s*->[^;]*)?\s*;\n',
        '',
        src,
        flags=re.MULTILINE
    )

# ─────────────────────────────────────────────────────────────────────────────
# 4. Add lean_alloc_closure extern declaration if missing
# ─────────────────────────────────────────────────────────────────────────────
if 'lean_alloc_closure' in src and 'fn lean_alloc_closure' not in src:
    src = 'extern "C" { fn lean_alloc_closure(fun: *mut core::ffi::c_void, arity: u32, num_fixed: u32) -> *mut LeanObject; }\n' + src

# ─────────────────────────────────────────────────────────────────────────────
# 5. Add SendPtr wrapper for thread safety of *mut LeanTaskObject
# ─────────────────────────────────────────────────────────────────────────────
if 'struct SendPtr' not in src:
    sendptr = textwrap.dedent("""
    /// Safety wrapper: LeanTaskObject raw pointer accessed under TaskManager mutex.
    struct SendPtr<T>(*mut T);
    unsafe impl<T> Send for SendPtr<T> {}
    impl<T> SendPtr<T> {
        #[inline] fn get(&self) -> *mut T { self.0 }
    }
    """)
    # Insert after the use declarations block (before first pub or struct)
    src = re.sub(
        r'(use std::thread;\n)',
        r'\1' + sendptr,
        src,
        count=1
    )

# ─────────────────────────────────────────────────────────────────────────────
# 6. Fix thread::spawn with *mut LeanTaskObject
#    Wrap t in SendPtr before the spawn call
# ─────────────────────────────────────────────────────────────────────────────
# Pattern: "thread::spawn(move || {" where t is captured
src = re.sub(
    r'(\s*)(thread::spawn\(move \|\| \{(\s*)unsafe \{ save_stack_info\(false\); \})',
    lambda m: m.group(1) + 'let t_send = SendPtr(t);\n' + m.group(1) +
              'thread::spawn(move || {' + m.group(3) + 'unsafe { save_stack_info(false); }',
    src,
    count=1
)
# Now replace uses of bare `t` inside the spawn closure with `t_send.get()`
# This is tricky without knowing the closure bounds; do a targeted replace
src = re.sub(
    r'(tm\.run_task_locked\(&mut guard, )t(\);)',
    r'\1t_send.get()\2',
    src,
    count=1
)

# ─────────────────────────────────────────────────────────────────────────────
# 7. Fix MutexGuard::unlocked → drop(guard) + drop_and_relock pattern
#    The pattern appears 4 times. Replace each with a safe Rust equivalent.
#    Note: after drop(guard), we need to reacquire from the mutex.
#    In run_task_locked, the guard comes from self.inner.lock().unwrap().
#    In the standalone function, it comes from tm.inner.lock().unwrap().
# ─────────────────────────────────────────────────────────────────────────────

def replace_mutex_unlocked(src):
    """
    Replace MutexGuard::unlocked(guard, || { <body> }) with:
    drop(guard); <body>; guard = <MUTEX>.lock().unwrap();

    Since this is inside a &mut MutexGuard<'_, TaskManagerInner> parameter,
    we need to handle differently: the guard is passed by &mut reference.
    Replace with a helper macro that drops and reacquires.
    """
    # Count occurrences
    count = src.count('MutexGuard::unlocked(guard,')
    if count == 0:
        return src

    # Add the helper macro if not present
    if 'macro_rules! with_mutex_unlocked' not in src:
        macro = textwrap.dedent("""
        /// Temporarily drops a MutexGuard, executes a block, then reacquires.
        /// Replacement for unstable MutexGuard::unlocked.
        macro_rules! with_mutex_unlocked {
            ($guard:ident, $mutex:expr, $body:block) => {{
                drop(std::mem::replace($guard, unsafe { core::mem::zeroed() }));
                let _result = $body;
                *$guard = $mutex.lock().unwrap();
                _result
            }};
        }
        """)
        src = re.sub(
            r'(use std::thread;\n)',
            r'\1' + macro,
            src,
            count=1
        )

    # Replace: MutexGuard::unlocked(guard, || { <body> });
    # With: with_mutex_unlocked!(guard, self.inner, { <body> });
    # This requires knowing which mutex to re-lock — context-dependent.

    # For simplicity, replace with a direct drop + body + relock pattern
    # using a local helper. The guard in run_task_locked is `*guard` (a &mut ref).

    # Pattern 1-3: inside run_task_locked method (uses self.inner)
    # Pattern 4: in wait_for_tasks (uses tm.inner)

    # Replace all occurrences - simpler approach: use drop/reacquire inline
    # We'll do a regex replacement that handles the balanced braces manually

    i = 0
    occurrence = 0
    result = []
    while i < len(src):
        # Look for MutexGuard::unlocked(guard,
        pos = src.find('MutexGuard::unlocked(guard,', i)
        if pos == -1:
            result.append(src[i:])
            break

        result.append(src[i:pos])
        occurrence += 1

        # Find the closure start: either || { or || unsafe {
        rest = src[pos:]
        # Skip past "MutexGuard::unlocked(guard, || " or "MutexGuard::unlocked(guard, || unsafe "
        m = re.match(r'MutexGuard::unlocked\(guard, \|\|( unsafe)? \{', rest)
        if not m:
            # Can't parse, leave as is
            result.append(src[pos:pos+1])
            i = pos + 1
            continue

        is_unsafe = m.group(1) is not None
        header_end = pos + m.end()

        # Find the matching closing brace + ");"
        depth = 1
        j = header_end
        while j < len(src) and depth > 0:
            if src[j] == '{':
                depth += 1
            elif src[j] == '}':
                depth -= 1
            j += 1
        # j now points past the '}'
        # Expect ");" next
        closing = src[j:j+2]
        if closing == ');':
            j += 2
        elif closing.startswith(')'):
            j += 1

        body = src[header_end:j - (2 if closing == ');' else 1)]

        # Determine the mutex name based on occurrence
        if occurrence <= 3:
            mutex_expr = 'self.inner'
        else:
            mutex_expr = 'tm.inner'

        # Emit replacement
        indent = ''
        # Find indent of the original line
        line_start = src.rfind('\n', 0, pos) + 1
        indent_match = re.match(r'^(\s*)', src[line_start:pos])
        if indent_match:
            indent = indent_match.group(1)

        unsafe_kw = 'unsafe ' if is_unsafe else ''
        replacement = (
            f'drop(std::mem::replace(guard, {mutex_expr}.lock().unwrap()));\n'
            f'{indent}{unsafe_kw}{{\n'
            f'{body}\n'
            f'{indent}}}\n'
            f'{indent}*guard = {mutex_expr}.lock().unwrap();\n'
        )
        result.append(replacement)
        i = j

    return ''.join(result)

src = replace_mutex_unlocked(src)

# ─────────────────────────────────────────────────────────────────────────────
# 8. Fix: add_dep vs add_dep_raw
# ─────────────────────────────────────────────────────────────────────────────
src = src.replace('self.add_dep(t1, t2)', 'self.add_dep_raw(t1, t2)')

# ─────────────────────────────────────────────────────────────────────────────
# 9. Fix: *v as *mut LeanObject (non-primitive cast)
# ─────────────────────────────────────────────────────────────────────────────
src = src.replace('*v as *mut LeanObject', '&mut *v as *mut LeanObject')

# ─────────────────────────────────────────────────────────────────────────────
# 10. Fix: resolve() type mismatches
#     (*promise).result is *mut LeanObject, resolve() wants *mut LeanTaskObject
# ─────────────────────────────────────────────────────────────────────────────
src = src.replace(
    'tm.resolve((*promise).result, none)',
    'tm.resolve((*promise).result as *mut LeanTaskObject, none)'
)
src = src.replace(
    'tm.resolve((*p).result, some_value)',
    'tm.resolve((*p).result as *mut LeanTaskObject, some_value)'
)

# Fix: (*o).result = t type mismatch (result is *mut LeanObject, t is *mut LeanTaskObject)
src = src.replace(
    '(*o).result = t;',
    '(*o).result = t as *mut LeanObject;'
)

# ─────────────────────────────────────────────────────────────────────────────
# 11. Fix: lean_io_check_canceled return type (bool vs u8)
# ─────────────────────────────────────────────────────────────────────────────
src = re.sub(
    r'(pub unsafe extern "C" fn lean_io_check_canceled\(\) -> u8 \{[^}]*?)lean_io_check_canceled_core\(\)',
    r'\1lean_io_check_canceled_core() as u8',
    src,
    flags=re.DOTALL
)

# ─────────────────────────────────────────────────────────────────────────────
# 12. Fix: .as_ref() on raw pointer outside unsafe (line ~493)
# ─────────────────────────────────────────────────────────────────────────────
src = re.sub(
    r'let in_pool = current_task\(\)\s*\n\s*\.as_ref\(\)',
    'let in_pool = unsafe { current_task().as_ref() }',
    src
)

# ─────────────────────────────────────────────────────────────────────────────
# 13. Fix: lean_is_scalar called outside unsafe block
# ─────────────────────────────────────────────────────────────────────────────
src = src.replace(
    'while !lean_is_scalar(it) {',
    'while unsafe { !lean_is_scalar(it) } {'
)

# ─────────────────────────────────────────────────────────────────────────────
# 14. Fix: lean_io_check_canceled_core extern declaration (returns bool not u8)
# ─────────────────────────────────────────────────────────────────────────────
src = re.sub(
    r'fn lean_io_check_canceled_core\(\s*\)\s*->\s*u8\s*;',
    'fn lean_io_check_canceled_core() -> bool;',
    src
)

# ─────────────────────────────────────────────────────────────────────────────
# Write result
# ─────────────────────────────────────────────────────────────────────────────
if src != original:
    with open(path, 'w') as f:
        f.write(src)
    print(f"Patched {path}")
else:
    print(f"No changes made to {path}")
