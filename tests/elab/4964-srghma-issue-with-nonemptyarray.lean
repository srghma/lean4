/-!
Variants of issue #4964 using `Array`-backed nonempty containers.

These examples all fail for the same reason as the original report:
the nested inductive translation rewrites the recursive container to an
auxiliary `_nested.*` type, but dependent proofs still mention functions
such as `Array.size` that expect the original container.
-/

namespace Tests_NonEmptyArray_usingProp
  structure NonEmptyArray (α : Type) where
    toArray : Array α
    isNonEmpty : toArray.size > 0
    deriving Hashable, Ord, Repr, DecidableEq

  inductive Binder1 (e : Type)
    | Op : Binder1 e → NonEmptyArray String → Binder1 e

  inductive Binder2 (e : Type)
    | Op : Array (Binder2 e) → Binder2 e

  inductive BinderInductive (e : Type)
    | Op : NonEmptyArray (BinderInductive e) → BinderInductive e

  structure BinderStructure (e : Type) where
    op : NonEmptyArray (BinderStructure e)
end Tests_NonEmptyArray_usingProp

namespace Tests_NonEmptyArray_usingSubtype_abbrev
  abbrev NonEmptyArray (α : Type) := { arr : Array α // arr.size > 0 }

  inductive BinderInductive (e : Type)
    | Op : NonEmptyArray (BinderInductive e) → BinderInductive e

  structure BinderStructure (e : Type) where
    op : NonEmptyArray (BinderStructure e)
end Tests_NonEmptyArray_usingSubtype_abbrev

namespace Tests_NonEmptyArray_usingSubtype_def
  def NonEmptyArray (α : Type) := { arr : Array α // arr.size > 0 }

  inductive BinderInductive (e : Type)
    | Op : NonEmptyArray (BinderInductive e) → BinderInductive e

  structure BinderStructure (e : Type) where
    op : NonEmptyArray (BinderStructure e)
end Tests_NonEmptyArray_usingSubtype_def

namespace ManualSubtypeInStructure
  structure Binder (e : Type) where
    op : { arr : Array (Binder e) // arr.size > 0 }
end ManualSubtypeInStructure
