/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

prelude
public import Init.Prelude
public import Init.Core
public import Init.Data.Function
public import Init.Data.Float
public import Init.Data.Float32

public section

namespace FloatSpec.IEEE754

/--
Explicit binary64 representation used as the semantic bridge for `Float`.

This is intentionally *not* the runtime representation. The runtime still sees
Lean's primitive `Float`; this type is only for proofs.
-/
inductive FullFloat64 where
  | zero (sign : Bool) : FullFloat64
  | infinity (sign : Bool) : FullFloat64
  | nan (sign : Bool) (payload : Nat) : FullFloat64
  | finite (sign : Bool) (mantissa : Nat) (exponent : Int) : FullFloat64

/-- Explicit binary32 representation used as the semantic bridge for `Float32`. -/
inductive FullFloat32 where
  | zero (sign : Bool) : FullFloat32
  | infinity (sign : Bool) : FullFloat32
  | nan (sign : Bool) (payload : Nat) : FullFloat32
  | finite (sign : Bool) (mantissa : Nat) (exponent : Int) : FullFloat32

axiom encode64 : Float → FullFloat64
axiom decode64 : FullFloat64 → Float

axiom encode32 : Float32 → FullFloat32
axiom decode32 : FullFloat32 → Float32

axiom decode64_encode64 : ∀ x : Float, decode64 (encode64 x) = x
axiom encode64_decode64 : ∀ x : FullFloat64, encode64 (decode64 x) = x

axiom decode32_encode32 : ∀ x : Float32, decode32 (encode32 x) = x
axiom encode32_decode32 : ∀ x : FullFloat32, encode32 (decode32 x) = x

theorem encode64_injective : Function.Injective encode64 := by
  intro a b h
  have ha : decode64 (encode64 a) = decode64 (encode64 b) := by rw [h]
  simpa [decode64_encode64] using ha

theorem encode32_injective : Function.Injective encode32 := by
  intro a b h
  have ha : decode32 (encode32 a) = decode32 (encode32 b) := by rw [h]
  simpa [decode32_encode32] using ha

end FloatSpec.IEEE754

namespace Float

/--
Bridge axiom between the primitive float and its bit-level encoding.

This is the minimal assumption needed to connect the runtime primitive float
to a semantic wrapper based on raw bits.
-/
axiom ofBits_toBits : ∀ f : Float, Float.ofBits (Float.toBits f) = f

/-- The other direction of the bit-level roundtrip. -/
axiom toBits_ofBits : ∀ b : UInt64, Float.toBits (Float.ofBits b) = b

/-- `Float.toBits` is injective. -/
theorem toBits_injective : Function.Injective Float.toBits := by
  intro a b h
  have h' := congrArg Float.ofBits h
  simpa [ofBits_toBits] using h'

end Float

namespace Float32

/-- Bridge axiom for the 32-bit primitive float. -/
axiom ofBits_toBits : ∀ f : Float32, Float32.ofBits (Float32.toBits f) = f

/-- The other direction of the 32-bit bit-level roundtrip. -/
axiom toBits_ofBits : ∀ b : UInt32, Float32.toBits (Float32.ofBits b) = b

/-- `Float32.toBits` is injective. -/
theorem toBits_injective : Function.Injective Float32.toBits := by
  intro a b h
  have h' := congrArg Float32.ofBits h
  simpa [ofBits_toBits] using h'

end Float32
