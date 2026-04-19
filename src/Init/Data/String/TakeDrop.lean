/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
import Init.Data.String.Basic
import Init.Data.List.TakeDrop

public section

namespace String

@[simp] theorem take_empty (n : Nat) : "".take n = "" := rfl

@[simp] theorem drop_empty (n : Nat) : "".drop n = "" := rfl

@[simp] theorem take_zero (s : String) : s.take 0 = "" := by
  simp [take, Substring.take, Substring.toString, Substring.mk, toSubstring]
  rfl

@[simp] theorem drop_zero (s : String) : s.drop 0 = s := by
  simp [drop, Substring.drop, Substring.toString, Substring.mk, toSubstring]
  match s with | ⟨data⟩ => rfl

theorem take_append_drop (s : String) (n : Nat) : s.take n ++ s.drop n = s := by
  simp [take, drop, append]
  -- This would involve lemmas about Substring.take and Substring.drop
  sorry

@[simp] theorem length_take (s : String) (n : Nat) : (s.take n).length = min n s.length := by
  sorry

@[simp] theorem length_drop (s : String) (n : Nat) : (s.drop n).length = s.length - n := by
  sorry

theorem take_take (s : String) (n m : Nat) : (s.take n).take m = s.take (min n m) := by
  sorry

theorem drop_drop (s : String) (n m : Nat) : (s.drop n).drop m = s.drop (n + m) := by
  sorry

theorem takeWhile_append_dropWhile (s : String) (p : Char → Bool) : s.takeWhile p ++ s.dropWhile p = s := by
  sorry

@[simp] theorem takeWhile_empty (p : Char → Bool) : "".takeWhile p = "" := rfl

@[simp] theorem dropWhile_empty (p : Char → Bool) : "".dropWhile p = "" := rfl

end String
