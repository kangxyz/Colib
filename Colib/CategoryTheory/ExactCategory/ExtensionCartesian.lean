/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionCartesianComparison
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionFunctor

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionCartesian.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Cartesian universal properties for actual extension arrows -/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

/-- Every actual extension arrow has the strong cartesian factorization property
for the unchanged original Q projection. -/
theorem existsUnique_extensionFactor {x y z : E.ExtensionTotal}
    (f : x ⟶ z) (g : y ⟶ z)
    (w : E.extensionProjectionQObj y ⟶ E.extensionProjectionQObj x)
    (hw : E.extensionProjectionQMap g = w ≫ E.extensionProjectionQMap f) :
    ∃! h : y ⟶ x, E.extensionProjectionQMap h = w ∧ h ≫ f = g := by
  obtain ⟨t, e, l, hl⟩ := E.exists_extensionLift x w
  have hc : E.extensionProjectionQMap (l ≫ f) =
      (E.qIsoOfIso e).hom ≫ E.extensionProjectionQMap g := by
    rw [E.extensionProjectionQMap_comp, hl, hw, Category.assoc]
  obtain ⟨a, ha, haQ⟩ := E.exists_extensionComparisonIso (l ≫ f) g e hc
  let h := a.inv ≫ l
  have hcomp : h ≫ f = g := by
    dsimp only [h]
    rw [Category.assoc, ← ha]
    simp
  have hproj : E.extensionProjectionQMap h = w := by
    apply (cancel_epi (E.qIsoOfIso e).hom).1
    rw [← haQ, ← E.extensionProjectionQMap_comp]
    change E.extensionProjectionQMap (a.hom ≫ a.inv ≫ l) = _
    simp only [Iso.hom_inv_id_assoc]
    rw [haQ]
    exact hl
  refine ⟨h, ⟨hproj, hcomp⟩, ?_⟩
  intro h' hh'
  apply E.extensionTotalMiddle.map_injective
  change h'.base.hom = h.base.hom
  let : Mono f.base.hom := E.mono_of_inflation f.base.property
  apply (cancel_mono f.base.hom).1
  exact congrArg (fun k => k.base.hom) (hh'.2.trans hcomp.symm)

end CategoryTheory.ExactCategory.ExactStructure
