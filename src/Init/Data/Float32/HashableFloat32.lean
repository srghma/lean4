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
public import Init.Data.Float32
public import Init.Data.Float.Bridge
public import Init.Data.Hashable
public import Init.Data.LawfulHashable
public import Init.Data.ToString.Basic

public section

/-- Bit pattern used for negative zero in IEEE-754 binary32. -/
def Float32.negZeroBits : UInt32 := 0x80000000

/--
A hashable float32 representation based on raw IEEE-754 bits.

The wrapper stores the bit pattern and only allows non-NaN values that are not
negative zero. The coercion back to `Float32` is the corresponding `ofBits`.
-/
structure HashableFloat32 where
  toFloat : Float32
  noNaN : toFloat.isNaN = false
  noNegZero : Float32.toBits toFloat ≠ Float32.negZeroBits

namespace HashableFloat32

/-- Coerce the wrapper back to a primitive `Float32`. -/
instance : Coe HashableFloat32 Float32 where
  coe f := f.toFloat

/-- Construct a hashable float32 from a primitive `Float32`. -/
def ofFloat (f : Float32) : Option HashableFloat32 :=
  if hNaN : f.isNaN = false then
    if hZero : Float32.toBits f = Float32.negZeroBits then
      none
    else
      some
        { toFloat := f
          noNaN := hNaN
          noNegZero := hZero }
  else
    none

theorem ext {a b : HashableFloat32} (h : a.toFloat = b.toFloat) : a = b := by
  cases a
  cases b
  cases h
  simp

instance : BEq HashableFloat32 where
  beq a b := Float32.toBits a.toFloat == Float32.toBits b.toFloat

instance : ReflBEq HashableFloat32 where
  rfl {a} := by
    simp [BEq.beq]

instance : LawfulBEq HashableFloat32 where
  eq_of_beq {a b} h := by
    have hbits : Float32.toBits a.toFloat == Float32.toBits b.toFloat := by
      simpa [BEq.beq] using h
    have hbits' : Float32.toBits a.toFloat = Float32.toBits b.toFloat := beq_iff_eq.mp hbits
    have hfloat : a.toFloat = b.toFloat := Float32.toBits_injective hbits'
    exact ext hfloat

instance : Hashable HashableFloat32 where
  hash f := hash (Float32.toBits f.toFloat)

instance : LawfulHashable HashableFloat32 where
  hash_eq a b h := by
    have hbits : Float32.toBits a.toFloat == Float32.toBits b.toFloat := by
      simpa [BEq.beq] using h
    have hbits' : Float32.toBits a.toFloat = Float32.toBits b.toFloat := beq_iff_eq.mp hbits
    have hfloat : a.toFloat = b.toFloat := Float32.toBits_injective hbits'
    change hash (Float32.toBits a.toFloat) = hash (Float32.toBits b.toFloat)
    rw [hfloat]

instance : ToString HashableFloat32 where
  toString f := toString f.toFloat

end HashableFloat32
