/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

prelude

public section

namespace FloatSpec.IEEE754

/--
IEEE 754 "full" float representation.

This is the minimal core we want to keep in Lean for the FloatSpec port.
It is intentionally separate from Lean's primitive `Float`.
-/
inductive FullFloat where
  | zero (sign : Bool) : FullFloat
  | infinity (sign : Bool) : FullFloat
  | nan (sign : Bool) (payload : Nat) : FullFloat
  | finite (sign : Bool) (mantissa : Nat) (exponent : Int) : FullFloat

/--
IEEE 754 "standard" float representation.

This folds all NaN payloads into a single constructor.
-/
inductive StandardFloat where
  | zero (sign : Bool) : StandardFloat
  | infinity (sign : Bool) : StandardFloat
  | nan : StandardFloat
  | finite (sign : Bool) (mantissa : Nat) (exponent : Int) : StandardFloat

/-- Collapse the full representation to the standard one. -/
def FF2SF : FullFloat → StandardFloat
  | .zero s => .zero s
  | .infinity s => .infinity s
  | .nan _ _ => .nan
  | .finite s m e => .finite s m e

/-- Inject the standard representation into the full one. -/
def SF2FF : StandardFloat → FullFloat
  | .zero s => .zero s
  | .infinity s => .infinity s
  | .nan => .nan false 0
  | .finite s m e => .finite s m e

/-- A NaN classifier on the full representation. -/
def isNaN : FullFloat → Bool
  | .nan _ _ => true
  | _ => false

/-- A finiteness classifier on the full representation. -/
def isFinite : FullFloat → Bool
  | .finite _ _ _ => true
  | .zero _ => true
  | _ => false

/-- Sign bit extraction on the full representation. -/
def sign : FullFloat → Bool
  | .zero s => s
  | .infinity s => s
  | .nan s _ => s
  | .finite s _ _ => s

theorem FF2SF_SF2FF (x : StandardFloat) : FF2SF (SF2FF x) = x := by
  cases x <;> rfl

theorem SF2FF_FF2SF (x : FullFloat) : SF2FF (FF2SF x) = x := by
  cases x <;> rfl

end FloatSpec.IEEE754

