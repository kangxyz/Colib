/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.QConstruction.Basic
public import Colib.Topology.ClassifyingSpace.Basic

/-!
# The homotopy groups of the restricted-span classifying space

This combines two genuine constructions: the category of spans modulo
isomorphism, and the geometric realization of its nerve. It is a generic
construction on a restricted-span calculus with a chosen object. The exact
category specialization in `Colib.KTheory.Quillen.Basic` obtains the hypotheses from the
proved exact-structure interface.

## Implementation provenance

Adapted from `Quillen/KTheory/QHomotopy.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The two abbreviations retain all
seven restricted-span hypotheses and the arbitrary distinguished object.
The original `Q` object is the existing `CategoryTheory.QConstruction`.
-/
@[expose] public section

noncomputable section

universe v u

open CategoryTheory

namespace CategoryTheory.QConstruction

variable {C : Type u} [Category.{v} C]
  (deflation inflation : MorphismProperty C)
  [deflation.ContainsIdentities] [inflation.ContainsIdentities]
  [deflation.IsStableUnderComposition] [inflation.IsStableUnderComposition]
  [deflation.HasPullbacksAgainst inflation]
  [deflation.IsStableUnderBaseChangeAgainst inflation]
  [inflation.IsStableUnderBaseChangeAgainst deflation]

/-- The actual realization of the nerve of the restricted-span category. -/
abbrev classifyingSpace := ClassifyingSpace (QConstruction deflation inflation)

/-- The shifted homotopy group at the distinguished object `zero`.
No claim that `zero` is a zero object in the Q-category is made or needed. -/
abbrev HomotopyGroup (zero : C) (n : ℕ) :=
  ShiftedHomotopyGroup (QConstruction deflation inflation)
    (QConstruction.of deflation inflation zero) n

/-- Group structure in every nonnegative K-style degree. -/
example (zero : C) (n : ℕ) : Group (HomotopyGroup deflation inflation zero n) :=
  inferInstance

/-- Commutativity in positive K-style degree, from higher homotopy groups. -/
example (zero : C) (n : ℕ) : CommGroup (HomotopyGroup deflation inflation zero (n + 1)) :=
  inferInstance

end CategoryTheory.QConstruction

attribute [colib_tag "COL-0044",
  colib_ref "WeibelKBook" "IV, Definition 6.3, shifted homotopy-group formula" "generalization"
    "Shifted homotopy groups of a restricted-span category at an arbitrary chosen object"]
  CategoryTheory.QConstruction.HomotopyGroup
