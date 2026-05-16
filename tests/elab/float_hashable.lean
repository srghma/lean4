import Init.Data.Float.HashableFloat
import Init.Data.Float32.HashableFloat32
import Std.Data.HashMap

/-! Regression test for hashable wrappers around `Float` and `Float32`.

The test exercises the wrapper constructors and verifies that the resulting
types behave as usable `Std.HashMap` keys. -/

open HashableFloat
open HashableFloat32

def hf : HashableFloat := by
  refine ⟨(1.5 : Float), ?_, ?_⟩
  · native_decide
  · native_decide

def hf32 : HashableFloat32 := by
  refine ⟨(1.5 : Float32), ?_, ?_⟩
  · native_decide
  · native_decide

def floatMap : Std.HashMap HashableFloat String :=
  (∅ : Std.HashMap HashableFloat String).insert hf "ok"

def float32Map : Std.HashMap HashableFloat32 String :=
  (∅ : Std.HashMap HashableFloat32 String).insert hf32 "ok"

example : floatMap.get? hf = some "ok" := by
  simp [floatMap, hf]

example : float32Map.get? hf32 = some "ok" := by
  simp [float32Map, hf32]

example : (HashableFloat.ofFloat (1.5 : Float)).isSome := by
  native_decide

example : (HashableFloat32.ofFloat (1.5 : Float32)).isSome := by
  native_decide
