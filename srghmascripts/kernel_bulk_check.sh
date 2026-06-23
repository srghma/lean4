#!/usr/bin/env bash
# TDD regression target for the Rust kernel type-checker's UAF on real declaration types.
#
# `Kernel.check env {} ci.type` over many DIVERSE real declaration types currently triggers a
# layout-sensitive over-free (use-after-free) that core-dumps after enough constants. The
# hand-built small-expr cases in `kernel_tc_suite.sh` never hit it (they exercise only simple
# shapes). This script reproduces it by sweeping real constant types from an `import Lean` env.
#
# Status semantics:
#   - PASS  : the range completed (printed DONE) and the process exited cleanly (no core dump).
#   - FAIL  : core dump (exit >128) or the loop aborted before DONE  -> the bug is present.
#
# It is also a GUARD for the session-4 leak fix (ensure_*_core consume + lean_kernel_* arg dec):
# reverting those drops the crash threshold from ~1000 back to ~20, so even the small ranges fail.
#
# The corruption surfaces as either a core dump (SIGSEGV) or a reduction hang (timeout); both
# count as FAIL. Each range runs under a 90s timeout, so the whole script stays under the 4-min/
# test budget.
#
# Numeric ranges [0:hi] are flaky (the over-free is ASLR/scheduling sensitive at small scale);
# sweeping the WHOLE environment (`all`, the default) reproduces it reliably (crashes within ~50s).
#
# Usage: srghmascripts/kernel_bulk_check.sh [all | HI ...]   (default: all)
set -u
LEAN=build/release/stage1/bin/lean
RANGES=("${@:-all}")
# shellcheck disable=SC2206
RANGES=(${RANGES[@]})

pass=0; fail=0
run_range() { # $1 = hi  ("all" = every constant, or a numeric upper bound)
  local hi="$1"
  local loop
  if [ "$hi" = "all" ]; then
    loop='for (_, ci) in env.constants.toList do'
  else
    loop="let cs := env.constants.toList
  for i in [0:$hi] do
   if h : i < cs.length then
    let ci := (cs[i]'h).2"
  fi
  local f; f=$(mktemp /tmp/kbulk_XXXX.lean)
  cat > "$f" <<EOF
import Lean
open Lean
set_option linter.unusedVariables false
def stress : CoreM Unit := do
  let env ← getEnv
  let mut ok := 0
  let mut err := 0
  $loop
      match Kernel.check env {} ci.type with
      | .ok _    => ok := ok + 1
      | .error _ => err := err + 1
  IO.println s!"DONE ok={ok} err={err}"
#eval stress
EOF
  local out; out=$(timeout 180 "$LEAN" "$f" 2>/dev/null); local ec=$?
  rm -f "$f"
  local done; done=$(printf '%s\n' "$out" | grep -c '^DONE ')
  if [ "$ec" -gt 128 ]; then
    printf '  FAIL  [%-5s] CRASH(exit=%s, signal=%s)\n' "$hi" "$ec" "$((ec-128))"; fail=$((fail+1))
  elif [ "$done" -ge 1 ]; then
    printf '  PASS  [%-5s] %s\n' "$hi" "$(printf '%s\n' "$out" | grep '^DONE ')"; pass=$((pass+1))
  else
    printf '  FAIL  [%-5s] no DONE marker (aborted, exit=%s)\n' "$hi" "$ec"; fail=$((fail+1))
  fi
}

for hi in "${RANGES[@]}"; do run_range "$hi"; done
echo "  -------- $pass passed, $fail failed --------"
[ "$fail" -eq 0 ]
