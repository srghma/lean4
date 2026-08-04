# [Transitive](https://en.wikipedia.org/wiki/Transitive_relation) [Binary Relations](https://en.wikipedia.org/wiki/Binary_relation)

All definitions tacitly require the [homogeneous relation](https://en.wikipedia.org/wiki/Homogeneous_relation) R to be transitive: for all a, b, c, if aRb and bRc then aRc.
A term's definition may require additional properties that are not listed in this table.

| | [Symmetric](https://en.wikipedia.org/wiki/Symmetric_relation) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsSymm) | [Antisymmetric](https://en.wikipedia.org/wiki/Antisymmetric_relation) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsAntisymm) | [Connected](https://en.wikipedia.org/wiki/Connected_relation) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsTotal) | [Well-founded](https://en.wikipedia.org/wiki/Well-founded_relation) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsWellFounded) | [Has joins](https://en.wikipedia.org/wiki/Join_and_meet) | [Has meets](https://en.wikipedia.org/wiki/Join_and_meet) | [Reflexive](https://en.wikipedia.org/wiki/Reflexive_relation) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsRefl) | [Irreflexive](https://en.wikipedia.org/wiki/Reflexive_relation#Irreflexive) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsIrrefl) | [Asymmetric](https://en.wikipedia.org/wiki/Asymmetric_relation) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsAsymm) |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| | | | Total, Semiconnex | | | | | Anti-reflexive | |
| [Equivalence relation](https://en.wikipedia.org/wiki/Equivalence_relation) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsEquiv) | ✅ | ✗ | ✗ | ✗ | ✗ | ✗ | ✅ | ✗ | ✗ |
| [Preorder (Quasiorder)](https://en.wikipedia.org/wiki/Preorder) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsPreorder) | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | ✅ | ✗ | ✗ |
| [Partial order](https://en.wikipedia.org/wiki/Partial_order) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsPartialOrder) | ✗ | ✅ | ✗ | ✗ | ✗ | ✗ | ✅ | ✗ | ✗ |
| [Total preorder](https://en.wikipedia.org/wiki/Total_preorder) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsLinearOrder) | ✗ | ✗ | ✅ | ✗ | ✗ | ✗ | ✅ | ✗ | ✗ |
| [Total order](https://en.wikipedia.org/wiki/Total_order) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsLinearOrder) | ✗ | ✅ | ✅ | ✗ | ✗ | ✗ | ✅ | ✗ | ✗ |
| [Prewellordering](https://en.wikipedia.org/wiki/Prewellordering) | ✗ | ✗ | ✅ | ✅ | ✗ | ✗ | ✅ | ✗ | ✗ |
| [Well-quasi-ordering](https://en.wikipedia.org/wiki/Well-quasi-ordering) | ✗ | ✗ | ✗ | ✅ | ✗ | ✗ | ✅ | ✗ | ✗ |
| [Well-ordering](https://en.wikipedia.org/wiki/Well-order) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsWellOrder) | ✗ | ✅ | ✅ | ✅ | ✗ | ✗ | ✅ | ✗ | ✗ |
| [Lattice](https://en.wikipedia.org/wiki/Lattice_(order)) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Lattice.html#Lattice) | ✗ | ✅ | ✗ | ✗ | ✅ | ✅ | ✅ | ✗ | ✗ |
| [Join-semilattice](https://en.wikipedia.org/wiki/Join-semilattice) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Lattice.html#SemilatticeSup) | ✗ | ✅ | ✗ | ✗ | ✅ | ✗ | ✅ | ✗ | ✗ |
| [Meet-semilattice](https://en.wikipedia.org/wiki/Meet-semilattice) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Lattice.html#SemilatticeInf) | ✗ | ✅ | ✗ | ✗ | ✗ | ✅ | ✅ | ✗ | ✗ |
| [Strict partial order](https://en.wikipedia.org/wiki/Strict_partial_order) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsStrictOrder) | ✗ | ✅ | ✗ | ✗ | ✗ | ✗ | ✗ | ✅ | ✅ |
| [Strict weak order](https://en.wikipedia.org/wiki/Weak_ordering#Strict_weak_orderings) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsStrictWeakOrder) | ✗ | ✅ | ✗ | ✗ | ✗ | ✗ | ✗ | ✅ | ✅ |
| [Strict total order](https://en.wikipedia.org/wiki/Strict_total_order) [∀](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/Unbundled.html#IsStrictTotalOrder) | ✗ | ✅ | ✅ | ✗ | ✗ | ✗ | ✗ | ✅ | ✅ |

✅ indicates the property is always true for that relation type. ✗ indicates it is not guaranteed (may or may not hold).

NOTE: Asymm ✅ + [Std.Total](https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/Init/Core.lean#L2582)/Connected ✅ = Trichotomous (Divided into three parts. for all x and y in X, and for a binary relation R, exactly one of xRy, yRx or x=y holds)
