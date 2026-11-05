/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.QCategory
public import Mathlib.CategoryTheory.IsConnected

/-! # Connectedness of the Q-category

Every object receives a particular arrow from the vertex represented by zero.
This proves connectedness of the category, without claiming uniqueness of these
arrows or that the chosen vertex is an initial or zero object in Q.

## Implementation provenance

Adapted from `Quillen/CategoryTheory/QConstruction/Connected.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original selected exact structure,
object and morphism universes, distinguished vertex and actual span maps are retained.

-/
@[expose] public noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- The distinguished object of Q, corresponding to zero in the original category. -/
abbrev qZero : E.QCategory := CategoryTheory.QConstruction.of E.deflation E.inflation (0 : C)

/-- The identity/zero admissible span supplies one arrow from the distinguished
vertex to any object. This does not assert that there is only one such arrow. -/
def fromZero (X : E.QCategory) : E.qZero ⟶ X :=
  CategoryTheory.QConstruction.mkHom E.deflation E.inflation
    { apex := 0
      l := 𝟙 _
      r := 0
      wl := E.deflation_id _
      wr := E.inflation_zero X.obj.of }

instance qCategory_nonempty : Nonempty E.QCategory := ⟨E.qZero⟩

/-- The Q-category is connected, by the zigzags X ← 0 → Y. -/
instance qCategory_isConnected : IsConnected E.QCategory := by
  apply IsConnected.of_constant_of_preserves_morphisms
  intro α f hf X Y
  exact (hf (E.fromZero X)).symm.trans (hf (E.fromZero Y))

end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_tag "COL-0039",
  colib_ref "WeibelKBook"
    "IV, paragraph preceding Proposition 6.2, paths from the zero vertex" "adaptation"
    "Categorical connectedness from chosen arrows out of the distinguished zero vertex"]
  CategoryTheory.ExactCategory.ExactStructure.qCategory_isConnected

attribute [colib_ref "WeibelKBook"
    "IV, paragraph preceding Proposition 6.2, paths from the zero vertex" "adaptation"
    "The particular identity/zero span gives an arrow; uniqueness is not asserted"]
  CategoryTheory.ExactCategory.ExactStructure.fromZero
