/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.FlagPresentation
public import Colib.CategoryTheory.Waldhausen.Rows.Reindex


/-! # Completion of admissible flags commutes with restriction -/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen.QuotientRows

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C) {m n : SimplexCategory}
variable (A : Fin (n.len + 1) ⥤ C)
variable (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f))

/-- The canonical cokernel completion is strictly compatible with restriction. -/
theorem quotientDiagram_reindex (α : m ⟶ n) :
    quotientDiagram E ((SimplexCategory.toCat.map α).toFunctor ⋙ A)
      (fun f ↦ hA ((SimplexCategory.toCat.map α).toFunctor.map f)) =
      indexMap α ⋙ quotientDiagram E A hA := rfl

/-- Restriction of a completed row is the completion of the restricted flag. -/
def flagRowReindexIso (α : m ⟶ n) :
    ((reindex (ofExactCategory E) α).obj (flagRow E A hA)).obj ≅
      (flagRow E ((SimplexCategory.toCat.map α).toFunctor ⋙ A)
        (fun f ↦ hA ((SimplexCategory.toCat.map α).toFunctor.map f))).obj := Iso.refl _

@[reassoc (attr := simp)]
theorem flagQuotient_reindex (α : m ⟶ n) (p : Interval m) :
    flagQuotient E ((SimplexCategory.toCat.map α).toFunctor ⋙ A)
      (fun f ↦ hA ((SimplexCategory.toCat.map α).toFunctor.map f)) p =
      flagQuotient E A hA ((indexMap α).obj p) := rfl

end CategoryTheory.Waldhausen.QuotientRows
