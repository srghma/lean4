/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.String.Basic
public import Init.Data.Slice.Basic
public import Init.Data.Slice.Notation
public import Init.Data.Range.Polymorphic.Nat

public section

namespace String

/--
A region of some underlying string.

A `String.Slice` is an abbreviation for `Std.Slice Substring`.
-/
abbrev Slice := Std.Slice Substring

/--
Converts a string into a slice that contains the entire string.
-/
@[inline, coe]
def toSlice (s : String) : Slice :=
  Std.Slice.mk s.toSubstring

instance : Coe String Slice := ⟨toSlice⟩

/--
Returns `true` if the string is non-empty and its first character satisfies `p`.
-/
@[inline]
def startsWith (s : String) (p : Char → Bool) : Bool :=
  !s.isEmpty && p (s.get 0)

/--
Returns `true` if the string is non-empty and its last character satisfies `p`.
-/
@[inline]
def endsWith (s : String) (p : Char → Bool) : Bool :=
  !s.isEmpty && p (s.get (s.prev s.endPos))

/--
Removes leading whitespace from a string, returning a slice.
-/
@[inline]
def trimAsciiStart (s : String) : Slice :=
  Std.Slice.mk s.toSubstring.trimLeft

/--
Removes trailing whitespace from a string, returning a slice.
-/
@[inline]
def trimAsciiEnd (s : String) : Slice :=
  Std.Slice.mk s.toSubstring.trimRight

/--
Removes leading and trailing whitespace from a string, returning a slice.
-/
@[inline]
def trimAscii (s : String) : Slice :=
  Std.Slice.mk s.toSubstring.trim

end String

namespace Std.Slice

open Std.PRange

/-- Extensionality for slices. -/
theorem ext {γ : Type u} {s₁ s₂ : Slice γ} (h : s₁.internalRepresentation = s₂.internalRepresentation) : s₁ = s₂ :=
  match s₁, s₂ with | mk r1, mk r2 => h ▸ rfl

instance {shape : RangeShape} :
    Sliceable shape String String.Pos String.Slice where
  mkSlice s range :=
    let stop := s.endPos
    let halfOpenRange := ClosedOpenIntersection.intersection range 0...<stop
    Std.Slice.mk ⟨s, halfOpenRange.lower, halfOpenRange.upper⟩

instance {shape : RangeShape} :
    Sliceable shape Substring String.Pos String.Slice where
  mkSlice s range :=
    let start := s.startPos
    let stop := s.stopPos
    let halfOpenRange := ClosedOpenIntersection.intersection range start...<stop
    Std.Slice.mk ⟨s.str, halfOpenRange.lower, halfOpenRange.upper⟩

instance : Self Substring String.Slice where
  eq := rfl

end Std.Slice

namespace String

theorem trimAsciiStart_eq_toSlice_of_not_startsWith (s : String) (p : Char → Bool) (h : ¬ s.startsWith p) :
    s.trimAsciiStart = s.toSlice := by
  simp [trimAsciiStart, toSlice, startsWith] at *
  if h_empty : s.isEmpty then
    simp [h_empty]
    apply Std.Slice.ext
    simp [toSubstring, h_empty, Substring.trimLeft, Substring.dropWhile]
    rfl
  else
    simp [h_empty] at h
    apply Std.Slice.ext
    simp [toSubstring, Substring.trimLeft, Substring.dropWhile]
    match s with
    | ⟨data⟩ =>
      simp [isEmpty, endPos, Pos.byteIdx] at h_empty
      match data with
      | [] => contradiction
      | c :: cs =>
        simp [get, next, Substring.dropWhile, Substring.takeWhileAux]
        simp [h]
        rfl

theorem eq_trimAsciiStart_of_not_startsWith_isWhitespace (s : String) (h : ¬ s.startsWith Char.isWhitespace = true) :
    s.trimAsciiStart = s.toSlice :=
  trimAsciiStart_eq_toSlice_of_not_startsWith s Char.isWhitespace (by simpa using h)

theorem trimAsciiEnd_eq_toSlice_of_not_endsWith (s : String) (p : Char → Bool) (h : ¬ s.endsWith p) :
    s.trimAsciiEnd = s.toSlice := by
  simp [trimAsciiEnd, toSlice, endsWith] at *
  if h_empty : s.isEmpty then
    simp [h_empty]
    apply Std.Slice.ext
    simp [toSubstring, h_empty, Substring.trimRight, Substring.dropRightWhile]
    rfl
  else
    simp [h_empty] at h
    apply Std.Slice.ext
    simp [toSubstring, Substring.trimRight, Substring.dropRightWhile]
    match s with
    | ⟨data⟩ =>
      simp [isEmpty, endPos, Pos.byteIdx] at h_empty
      -- Implementation details of dropRightWhile would be needed for a full proof
      sorry

theorem eq_trimAsciiEnd_of_not_endsWith_isWhitespace (s : String) (h : ¬ s.endsWith Char.isWhitespace = true) :
    s.trimAsciiEnd = s.toSlice :=
  trimAsciiEnd_eq_toSlice_of_not_endsWith s Char.isWhitespace (by simpa using h)

theorem eq_trimAscii_of_not_startsWith_and_not_endsWith (s : String) (h1 : ¬ s.startsWith Char.isWhitespace = true) (h2 : ¬ s.endsWith Char.isWhitespace = true) :
    s.trimAscii = s.toSlice := by
  simp [trimAscii, toSlice]
  apply Std.Slice.ext
  have h1' : ¬ s.startsWith Char.isWhitespace := by simpa using h1
  have h2' : ¬ s.endsWith Char.isWhitespace := by simpa using h2
  -- Combine both by showing trim = id if no leading/trailing whitespace
  sorry

/-- A string slice can be converted back to a string. -/
def Slice.toString (s : Slice) : String :=
  s.internalRepresentation.toString

instance : ToString Slice where
  toString := Slice.toString

@[simp] theorem trimAscii_toString (s : String) : s.trimAscii.toString = s.trim := rfl
@[simp] theorem trimAsciiStart_toString (s : String) : s.trimAsciiStart.toString = s.trimLeft := rfl
@[simp] theorem trimAsciiEnd_toString (s : String) : s.trimAsciiEnd.toString = s.trimRight := rfl

@[simp] theorem toSlice_toString (s : String) : s.toSlice.toString = s := by
  simp [toSlice, Slice.toString, toSubstring, Substring.toString]

theorem trimAscii_idempotent (s : String) : s.trimAscii.toString.trimAscii = s.trimAscii := by
  apply Std.Slice.ext
  simp [Slice.toString, trimAscii]
  -- Substring.trim is idempotent in a sense
  sorry

end String
