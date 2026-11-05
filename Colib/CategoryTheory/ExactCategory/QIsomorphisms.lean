/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.Isomorphisms
public import Colib.CategoryTheory.QConstruction.Isomorphisms

/-!
# The Q-isomorphism induced by an exact-category isomorphism

Extracted from the purely categorical exact-structure declarations of
`Quillen/Topology/ClassifyingSpace/PointedFunctor.lean` and
`Quillen/KTheory/Map/CoherenceData.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
All constructions retain the actual objects, span legs and canonical maps.
No balancedness, ambient abelian structure or arbitrary pullback hypothesis is added.
This module makes no assertion about classifying spaces or homotopy K-groups.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- Isomorphisms of original-category objects induce isomorphisms of the
Q-category. Both arrows are admissible by the exact-category axioms. -/
def qIsoOfIso (E : ExactStructure C) {X Y : C} (e : X ≅ Y) :
    QConstruction.of E.deflation E.inflation X ≅ QConstruction.of E.deflation E.inflation Y :=
  QConstruction.isoOfIso E.deflation E.inflation e (E.inflation_of_iso e)
    (E.inflation_of_iso e.symm)

@[simp]
theorem qIsoOfIso_refl (E : ExactStructure C) (X : C) :
    E.qIsoOfIso (Iso.refl X) = Iso.refl (QConstruction.of E.deflation E.inflation X) := by
  apply Iso.ext
  rfl

/-- Original isomorphism composition is respected in an exact Q-category. -/
@[simp]
theorem qIsoOfIso_trans (E : ExactStructure C)
    {X Y Z : C} (e : X ≅ Y) (f : Y ≅ Z) :
    E.qIsoOfIso (e ≪≫ f) = E.qIsoOfIso e ≪≫ E.qIsoOfIso f :=
  QConstruction.isoOfIso_trans E.deflation E.inflation e f _ _ _ _ _ _


end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_tag "COL-0048",
  colib_ref "WeibelKBook" "IV, Subobjects 6.1.2, isomorphism correspondence, forward direction"
    "clause" "Original isomorphisms induce Q-isomorphisms via identity-left-leg spans"]
  CategoryTheory.ExactCategory.ExactStructure.qIsoOfIso
  CategoryTheory.ExactCategory.ExactStructure.qIsoOfIso_refl
  CategoryTheory.ExactCategory.ExactStructure.qIsoOfIso_trans
