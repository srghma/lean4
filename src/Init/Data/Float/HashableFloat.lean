/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

prelude
public import Init.Prelude
public import Init.Core
public import Init.Coe
public import Init.Data.OfScientific
public import Init.Data.Float
public import Init.Data.Float.Bridge
public import Init.Data.Hashable
public import Init.Data.LawfulHashable
public import Init.Data.ToString.Basic

public section

/-- Bit pattern used for negative zero in IEEE-754 binary64. -/
def Float.negZeroBits : UInt64 := 0x8000000000000000

/--
A hashable float representation based on raw IEEE-754 bits.

The wrapper stores the bit pattern and only allows non-NaN values that are not
negative zero. The coercion back to `Float` is the corresponding `ofBits`.
-/
structure HashableFloat where
  toFloat : Float
  noNaN : toFloat.isNaN = false
  noNegZero : toFloat ≠ (-0.0 : Float)

namespace HashableFloat

/-- Coerce the wrapper back to a primitive `Float`. -/
instance : Coe HashableFloat Float where
  coe f := f.toFloat

/-- Construct a hashable float from a primitive `Float`. -/
def ofFloat (f : Float) : Option HashableFloat :=
  if hNaN : f.isNaN = false then
    if hZero : Float.toBits f = Float.negZeroBits then
      none
    else
      some
        { toFloat := f
          noNaN := hNaN
          noNegZero := by
            intro hneg
            have hbits : Float.toBits f = Float.negZeroBits := by
              rw [hneg]
              simpa [Float.negZeroBits] using FloatSpec.IEEE754.toBits_negZero64
            simpa [Float.negZeroBits] using hZero hbits }
  else
    none

theorem ext {a b : HashableFloat} (h : a.toFloat = b.toFloat) : a = b := by
  cases a
  cases b
  cases h
  simp

instance : BEq HashableFloat where
  beq a b := Float.toBits a.toFloat == Float.toBits b.toFloat

instance : ReflBEq HashableFloat where
  rfl {a} := by
    simp [BEq.beq]

instance : LawfulBEq HashableFloat where
  eq_of_beq {a b} h := by
    have hbits : Float.toBits a.toFloat == Float.toBits b.toFloat := by
      simpa [BEq.beq] using h
    have hbits' : Float.toBits a.toFloat = Float.toBits b.toFloat := beq_iff_eq.mp hbits
    have hfloat : a.toFloat = b.toFloat := Float.toBits_injective hbits'
    exact ext hfloat

instance : Hashable HashableFloat where
  hash f := hash (Float.toBits f.toFloat)

instance : LawfulHashable HashableFloat where
  hash_eq a b h := by
    have hbits : Float.toBits a.toFloat == Float.toBits b.toFloat := by
      simpa [BEq.beq] using h
    have hbits' : Float.toBits a.toFloat = Float.toBits b.toFloat := beq_iff_eq.mp hbits
    have hfloat : a.toFloat = b.toFloat := Float.toBits_injective hbits'
    change hash (Float.toBits a.toFloat) = hash (Float.toBits b.toFloat)
    rw [hfloat]

instance : ToString HashableFloat where
  toString f := toString f.toFloat

end HashableFloat
