set_option linter.missingDocs false

namespace TestFloat

def nan : Float := 0.0 / 0.0

/-- info: false -/ #guard_msgs in #eval nan == nan
/-- info: true -/ #guard_msgs in #eval (0.0 : Float) == (-0.0 : Float)
/-- info: true -/ #guard_msgs in #eval (1.0 : Float) == (1.0 : Float)

example : nan = nan := rfl

/-- info: nan = nan -/ #guard_msgs in #reduce nan = nan
/-- error: failed to synthesize
  Decidable (nan = nan)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/ #guard_msgs in #eval nan = nan

def p (f : Float) := (f, Float.toBits f)

/-- info: (0.000000, 0) -/ #guard_msgs in #eval p (0.0)
/-- info: (2.000000, 4611686018427387904) -/ #guard_msgs in #eval p (2.0)
/-- info: (-0.000000, 9223372036854775808) -/ #guard_msgs in #eval p (-0.0)

/-- info: (NaN, 9221120237041090560) -/ #guard_msgs in #eval p (0.0 / 0.0)
/-- info: (NaN, 9221120237041090560) -/ #guard_msgs in #eval p (0.0 / -0.0)
/-- info: (NaN, 9221120237041090560) -/ #guard_msgs in #eval p (-0.0 / 0.0)
/-- info: (NaN, 9221120237041090560) -/ #guard_msgs in #eval p (-0.0 / -0.0)

/-- info: (-inf, 18442240474082181120) -/ #guard_msgs in #eval p (1.0 / -0.0)
/-- info: (inf, 9218868437227405312) -/ #guard_msgs in #eval p (1.0 / 0.0)
/-- info: (inf, 9218868437227405312) -/ #guard_msgs in #eval p (-1.0 / -0.0)
/-- info: (-inf, 18442240474082181120) -/ #guard_msgs in #eval p (-1.0 / 0.0)

end TestFloat

namespace TestFloat32

def nan : Float32 := 0.0 / 0.0

/-- info: false -/ #guard_msgs in #eval nan == nan
/-- info: true -/ #guard_msgs in #eval (0.0 : Float32) == (-0.0 : Float32)
/-- info: true -/ #guard_msgs in #eval (1.0 : Float32) == (1.0 : Float32)

example : nan = nan := rfl

/-- error: failed to synthesize
  Decidable (nan = nan)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/ #guard_msgs in #eval nan = nan

def p (f : Float32) := (f, Float32.toBits f)

/-- info: (0.000000, 0) -/ #guard_msgs in #eval p (0.0)
/-- info: (2.000000, 1073741824) -/ #guard_msgs in #eval p (2.0)
/-- info: (-0.000000, 2147483648) -/ #guard_msgs in #eval p (-0.0)

/-- info: (NaN, 2143289344) -/ #guard_msgs in #eval p (0.0 / 0.0)
/-- info: (NaN, 2143289344) -/ #guard_msgs in #eval p (0.0 / -0.0)
/-- info: (NaN, 2143289344) -/ #guard_msgs in #eval p (-0.0 / 0.0)
/-- info: (NaN, 2143289344) -/ #guard_msgs in #eval p (-0.0 / -0.0)

/-- info: (-inf, 4286578688) -/ #guard_msgs in #eval p (1.0 / -0.0)
/-- info: (inf, 2139095040) -/ #guard_msgs in #eval p (1.0 / 0.0)
/-- info: (inf, 2139095040) -/ #guard_msgs in #eval p (-1.0 / -0.0)
/-- info: (-inf, 4286578688) -/ #guard_msgs in #eval p (-1.0 / 0.0)

end TestFloat32


namespace TestFloatLe

def nan : Float := 0.0 / 0.0
def inf : Float := 1.0 / 0.0
def negInf : Float := -1.0 / 0.0

-- 1. NaN is "Unordered"
-- IEEE 754 spec: Any comparison with NaN is false (except !=)
/-- info: false -/ #guard_msgs in #eval nan <= nan
/-- info: false -/ #guard_msgs in #eval nan < nan
/-- info: false -/ #guard_msgs in #eval nan <= 1.0
/-- info: false -/ #guard_msgs in #eval 1.0 <= nan

-- 2. Signed Zeros
-- IEEE 754 spec: 0.0 and -0.0 are treated as equal in comparisons
/-- info: true -/ #guard_msgs in #eval (0.0 : Float) <= (-0.0 : Float)
/-- info: true -/ #guard_msgs in #eval (-0.0 : Float) <= (0.0 : Float)
/-- info: false -/ #guard_msgs in #eval (0.0 : Float) < (-0.0 : Float)

-- 3. Infinities
/-- info: true -/ #guard_msgs in #eval negInf < 0.0
/-- info: true -/ #guard_msgs in #eval 0.0 < inf
/-- info: true -/ #guard_msgs in #eval negInf < inf

-- 4. Prop vs Decidable
-- 'a <= b' is a Prop. We can #eval it because Float.decLe is an instance.
-- When we #eval a Prop, Lean uses the Decidable instance to give us a Bool.
/-- info: true -/ #guard_msgs in #eval 1.0 <= 2.0

-- But in the kernel, it is still just a Prop:
example : 1.0 <= 2.0 := by
  -- we cannot use 'rfl' here because 1.0 <= 2.0 is not true by definition/reduction
  -- since 'le' is defined via 'opaque' floatSpec.
  decide

end TestFloatLe


/-
I dont understand

we have

set_option bootstrap.genMatcherCode false
/--
Strict inequality of floating-point numbers. Typically used via the `<` operator.
-/
def Float.lt : Float → Float → Prop := fun a b =>
  match a, b with
  | ⟨a⟩, ⟨b⟩ => floatSpec.lt a b

and

/--
Compares two floating point numbers for strict inequality.

This function does not reduce in the kernel. It is compiled to the C inequality operator.
-/
@[extern "lean_float_decLt"] opaque Float.decLt (a b : Float) : Decidable (a < b) :=
  match a, b with
  | ⟨a⟩, ⟨b⟩ => floatSpec.decLt a b

what is the difference between (1.0 <= 2.0 : Prop) and (1.0 <= 2.0 : Bool) and Float.decLt 1.0 2.0?

----

Prop will use lt
Bool will use decLt + Decidable.rec
-/

/-
-- But in the kernel, it is still just a Prop:
example : 1.0 <= 2.0 := by
  -- we cannot use 'rfl' here because 1.0 <= 2.0 is not true by definition/reduction
  -- since 'le' is defined via 'opaque' floatSpec.
  decide


Tactic `decide` failed for proposition
  1.0 ≤ 2.0
because its `Decidable` instance
  Float.decLe 1.0 2.0
did not reduce to `isTrue` or `isFalse`.

Reduction got stuck at the `Decidable` instance
  Float.decLe 1.0 2.0


but native_decide works

is there a reason not to make decide reduce completely?

what is it reduced to impartially?
-----

decide = Pure Logic. It fails because it doesn't have a "Floating Point Unit" inside the logic engine.
native_decide = Hardware Execution. It works because it asks your real CPU for the answer.
opaque = The reason the kernel stops. It protects the kernel from having to understand complex hardware-level data.


-/

#reduce (1.0 <= 2.0 : Bool)
#reduce (1.0 <= 2.0 : Decidable (1.0 <= 2.0))

#reduce Float.decLe
  (1.0) -- This is 1.0
  (Float.ofBits 4611686018427387904) -- This is 2.0
