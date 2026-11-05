/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.QCategory
public import Colib.CategoryTheory.QConstruction.HomotopyGroup

/-!
# Quillen K-groups of an exact category

For an exact structure `E`, the Q-category uses E's admissible epimorphisms
as left legs and admissible monomorphisms as right legs. All pullback-calculus
instances come from the exact-structure axioms and their proved consequences.
The basepoint is the vertex represented by the zero object of the original
additive category. We make no assertion that it is a zero object in Q.

This file gives the definition, not the K₀ comparison theorem or the deeper
structural theorems of algebraic K-theory.

## Implementation provenance

Adapted from `Quillen/KTheory/Basic.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The existing `QCategory` is imported
from its mathematical owner rather than defined again. The three remaining
named declarations retain the zero vertex and the `(n + 1)` shift.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Quillen's classifying space, the geometric realization of the Q-category's nerve. -/
abbrev KSpace := CategoryTheory.ClassifyingSpace E.QCategory

/-- The basepoint supplied by the original category's zero object. -/
def kBasepoint : E.KSpace :=
  CategoryTheory.classifyingSpacePoint
    (CategoryTheory.QConstruction.of E.deflation E.inflation (0 : C))

/-- The nonnegative Quillen K-group, defined by the shifted homotopy group
`π_(n+1)(|NQ(E)|, 0)`. -/
abbrev K (n : ℕ) :=
  CategoryTheory.QConstruction.HomotopyGroup E.deflation E.inflation (0 : C) n

/-- In every degree the construction inherits a group structure. -/
example (n : ℕ) : Group (E.K n) := inferInstance

/-- In strictly positive K-degree the group is commutative by higher homotopy
commutativity. K₀ commutativity requires a separate Q-specific theorem. -/
example (n : ℕ) : CommGroup (E.K (n + 1)) := inferInstance

end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_tag "COL-0045",
  colib_ref "WeibelKBook" "IV, Definition 6.3, shifted homotopy-group formula" "clause"
    "Nonnegative K-groups as the (n + 1)st homotopy groups of BQ at the original zero vertex"]
  CategoryTheory.ExactCategory.ExactStructure.K

attribute [colib_ref "WeibelKBook" "IV, Definition 6.1 and paragraph preceding Proposition 6.2"
    "adaptation" "The space BQ and its zero vertex, not the loop space KA used in Definition 6.3"]
  CategoryTheory.ExactCategory.ExactStructure.KSpace
  CategoryTheory.ExactCategory.ExactStructure.kBasepoint
