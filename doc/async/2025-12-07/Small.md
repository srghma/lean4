Today I decided to find what is the difference btw Small in Mathlib/Logic/Small/Basic.lean and Small in src/Init/Data/Iterators/Basic.lean

```
import Mathlib.Logic.Small.Basic
import Mathlib.Data.Real.Basic

#check Small Empty
#check Small (Type 1)
#check Small Real
#check Small (Set Real)
#check Small (Real → Real)
#check Small (ULift Nat)

def realsInTypeZero : Type := Shrink.{0} Real
instance : Small.{0} Real := inferInstance

#check Small.{0,0} (Type 0) -- fails
#check Small.{1,0} (Type 0) -- fails
#check Small.{0,1} (Type 0) #synth Small.{0,1} (Type 0) -- synth fails
#check Small.{1,1} (Type 0) #synth Small.{1,1} (Type 0) -- small_self
#check Small.{2,1} (Type 0) #synth Small.{2,1} (Type 0) -- small_succ
#check Small.{3,1} (Type 0) #synth Small.{3,1} (Type 0) -- failed to synthesize Small.{3, 1} Type

example : Small.{3, 1} (Type 0) := small_lift.{1,3,1} (Type 0)
-- example : Small.{32,32} (Type 31) := ⟨Type 31, ⟨rfl⟩⟩

#check Small.{0,0} (Type 1) -- fails
#check Small.{1,0} (Type 1) -- fails
#check Small.{0,1} (Type 1) -- fails
#check Small.{1,1} (Type 1) -- fails
#check Small.{0,2} (Type 1) #synth Small.{0,2} (Type 1) -- synth fails
#check Small.{1,2} (Type 1) #synth Small.{1,2} (Type 1) -- synth fails
#check Small.{2,2} (Type 1) #synth Small.{2,2} (Type 1) -- small_self
#check Small.{3,2} (Type 1) #synth Small.{3,2} (Type 1) -- small_self
#check Small.{4,2} (Type 1) #synth Small.{4,2} (Type 1) -- small_self

example : Small.{4,2} (Type 1) := small_lift.{2,4,2} (Type 1)
```
