#!/usr/bin/env bash
# Regression harness for the Rust kernel type-checker (Kernel.whnf / .check / .isDefEq).
# Each case runs in its own `lean` process so a segfault in one does not kill the suite.
# Usage: srghmascripts/kernel_tc_suite.sh
set -u
LEAN=build/release/stage1/bin/lean
PRELUDE='import Lean
open Lean
set_option linter.unusedVariables false
def W (a : Expr) : CoreM Unit := do
  let env ← getEnv
  IO.println (toString (← ofExceptKernelException (Kernel.whnf env {} a)))
def C (a : Expr) : CoreM Unit := do
  let env ← getEnv
  IO.println (toString (← ofExceptKernelException (Kernel.check env {} a)))
def D (a b : Expr) : CoreM Unit := do
  let env ← getEnv
  IO.println (toString (← ofExceptKernelException (Kernel.isDefEq env {} a b)))
-- check `a`, then whnf the resulting type (normalizes the inferred type for a stable assertion)
def CW (a : Expr) : CoreM Unit := do
  let env ← getEnv
  let t ← ofExceptKernelException (Kernel.check env {} a)
  IO.println (toString (← ofExceptKernelException (Kernel.whnf env {} t)))
-- (Sigma.mk Nat (fun _ => Nat) 1 2).snd : a VALID dependent projection (field type `β fst` has a
-- loose bvar) — exercises the infer_proj mk_proj branch, which over-freed the borrowed proj
-- subject / struct-name before a session-4d fix. Checking it in a loop catches that use-after-free.
def depProj : Expr :=
  Expr.proj `Sigma 1 <|
    mkApp4 (mkConst `Sigma.mk [Level.zero, Level.zero])
      (mkConst `Nat) (Expr.lam `x (mkConst `Nat) (mkConst `Nat) .default)
      (Expr.lit (.natVal 1)) (Expr.lit (.natVal 2))
-- whnf / isDefEq of named constants (exercises real elaborated terms incl. recursors)
def WN (n : Name) : CoreM Unit := do
  let env ← getEnv
  IO.println (toString (← ofExceptKernelException (Kernel.whnf env {} (mkConst n))))
def DN (a b : Name) : CoreM Unit := do
  let env ← getEnv
  IO.println (toString (← ofExceptKernelException (Kernel.isDefEq env {} (mkConst a) (mkConst b))))
def tcDecide : Bool := decide (1 < 2)
def tcStrLen : Nat := "hi".length
def tcAdd1 : Nat := 100 + 100
def tcAdd2 : Nat := 200
noncomputable def tcNatRec : Nat := Nat.rec (motive := fun _ => Nat) 5 (fun _ ih => ih.succ) (Nat.succ Nat.zero)
noncomputable def tcBoolRec : Bool := Bool.rec (motive := fun _ => Bool) false true true
def tcListLen : Nat := [10,20,30].length
def tcRatDivInt : Rat := Rat.divInt 1 2
def tcRatNum : Int := (Rat.divInt 1 2).num
def tcRatDen : Nat := (Rat.divInt 1 2).den
def tcRatLit : Rat := 1/2
def tcRatLitDen : Nat := (1/2 : Rat).den
def tcStrEq : Bool := decide ("hello" = "world")'

pass=0; fail=0
# run NAME EXPECTED EVAL-EXPR...
run() {
  local name="$1"; local expect="$2"; shift 2
  local f; f=$(mktemp /tmp/ktc_XXXX.lean)
  { printf '%s\n' "$PRELUDE"; printf '#eval %s\n' "$*"; } > "$f"
  local out; out=$(timeout 30 "$LEAN" "$f" 2>&1); local ec=$?
  rm -f "$f"
  local got; got=$(echo "$out" | grep -v 'deprecated\|^$' | head -1)
  if [ "$ec" -ne 0 ] && [ "$ec" -ne 1 ]; then
    printf '  CRASH(%s) %-22s\n' "$ec" "$name"; fail=$((fail+1))
  elif [ "$got" = "$expect" ]; then
    printf '  ok       %-22s = %s\n' "$name" "$got"; pass=$((pass+1))
  else
    printf '  WRONG    %-22s got[%s] want[%s]\n' "$name" "$got" "$expect"; fail=$((fail+1))
  fi
}

run whnf-beta       'Nat.zero' \
  'W (Expr.app (Expr.lam `x (mkConst `Nat) (Expr.bvar 0) .default) (mkConst `Nat.zero))'
run whnf-nat-succ   '1'        'W (mkApp (mkConst `Nat.succ) (mkConst `Nat.zero))'
run whnf-nat-add    '5'        'W (mkApp2 (mkConst `Nat.add) (Expr.lit (.natVal 2)) (Expr.lit (.natVal 3)))'
run whnf-nat-mul    '42'       'W (mkApp2 (mkConst `Nat.mul) (Expr.lit (.natVal 6)) (Expr.lit (.natVal 7)))'
run whnf-natlit     '100'      'W (mkNatLit 100)'
run whnf-proj       '7'        'W (Expr.proj `Prod 0 (mkApp4 (mkConst `Prod.mk [Level.zero, Level.zero]) (mkConst `Nat) (mkConst `Nat) (Expr.lit (.natVal 7)) (Expr.lit (.natVal 9))))'
run whnf-rec-decide 'Bool.true' 'WN `tcDecide'
run whnf-rec-strlen '2'         'WN `tcStrLen'
run defeq-rec-bignat 'true'     'DN `tcAdd1 `tcAdd2'
run check-nat       'Nat'      'C (mkApp2 (mkConst `Nat.add) (Expr.lit (.natVal 2)) (Expr.lit (.natVal 3)))'

# --- check-mode infer over binders: guards the session-4 leak fix (ensure_sort_core /
#     ensure_pi_core now CONSUME their first arg; infer_pi/infer_lambda/infer_let call sites).
#     A regression of that change reintroduces +1 refcount leaks per binder check. ---
run check-pi        'Type'            'C (Expr.forallE `x (mkConst `Nat) (mkConst `Nat) .default)'
run check-lam       'Nat -> Nat'      'C (Expr.lam `x (mkConst `Nat) (Expr.bvar 0) .default)'
run check-let       'Nat'             'C (Expr.letE `x (mkConst `Nat) (mkConst `Nat.zero) (Expr.bvar 0) false)'
# Dependent projection (infer_proj mk_proj-ordering use-after-free, session-4d). Looped so the
# use-after-free accumulates and crashes if the fix regresses; the type whnfs to `Nat`.
run check-dep-proj  'Nat'             'do for _ in [0:300] do CW depProj'

run defeq-lit       'true'     'D (Expr.lit (.natVal 5)) (Expr.lit (.natVal 5))'
run defeq-lit-ne    'false'    'D (Expr.lit (.natVal 5)) (Expr.lit (.natVal 6))'
run defeq-add       'true'     'D (mkApp2 (mkConst `Nat.add) (Expr.lit (.natVal 2)) (Expr.lit (.natVal 3))) (Expr.lit (.natVal 5))'
run defeq-add-big   'true'     'D (mkApp2 (mkConst `Nat.add) (Expr.lit (.natVal 100000000000)) (Expr.lit (.natVal 100000000000))) (Expr.lit (.natVal 200000000000))'
run defeq-const     'true'     'D (mkConst `Nat) (mkConst `Nat)'

# --- recursor reduction ---
run whnf-nat-rec    '6'         'WN `tcNatRec'
run whnf-bool-rec   'Bool.true' 'WN `tcBoolRec'
run whnf-list-len   '3'         'WN `tcListLen'

# --- universe-level normalization (sort comparison) ---
run defeq-lvl-max00 'true'  'D (Expr.sort (Level.max .zero .zero)) (Expr.sort .zero)'
run defeq-lvl-max01 'true'  'D (Expr.sort (Level.max .zero (.succ .zero))) (Expr.sort (.succ .zero))'
run defeq-lvl-imax  'true'  'D (Expr.sort (Level.imax (.succ .zero) (.succ .zero))) (Expr.sort (.succ .zero))'
run defeq-lvl-comm  'true'  'D (Expr.sort (Level.max (.param `u) (.param `v))) (Expr.sort (Level.max (.param `v) (.param `u)))'
run defeq-lvl-succ2 'true'  'D (Expr.sort (.succ (Level.max .zero .zero))) (Expr.sort (.succ .zero))'

# --- Rat reduction (grind_* depends on these) ---
run whnf-rat-den    '2'     'WN `tcRatDen'    # (Rat.divInt 1 2).den
run whnf-rat-num    'Int.ofNat 1' 'WN `tcRatNum'    # (Rat.divInt 1 2).num
run whnf-rat-litden '2'     'WN `tcRatLitDen' # (1/2 : Rat).den  -- HDiv.hDiv chain

# --- String reduction (kernel2 depends on these) ---
run whnf-str-len    '2'         'WN `tcStrLen'  # "hi".length
run whnf-str-eq     'Bool.false' 'WN `tcStrEq'  # decide ("hello" = "world")

echo "  -------- $pass passed, $fail failed --------"
