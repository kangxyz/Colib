/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.Basic

/-!
# Isomorphisms and admissible maps

Adapted from `Aglib/CategoryTheory/ExactCategory/Isomorphisms.lean` at Aglib commit
`2c34f185fa859e862661f939cd216b07bcccfb26`, together with only
`isIso_of_deflation_of_mono` from `Quillen/Aglib/CategoryTheory/ExactCategory/SpecialFractions.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The latter proof uses
only the actual cokernel universal property and requires no obscure axiom or
filtering machinery.
All constructions retain the actual objects, span legs and canonical maps.
No balancedness, ambient abelian structure or arbitrary pullback hypothesis is added.
This module makes no assertion about classifying spaces or homotopy K-groups.
-/

@[expose] public noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- Every isomorphism is an admissible monomorphism, since it is a kernel of
an admissible zero map to zero. -/
lemma inflation_of_iso {X Y : C} (e : X ≅ Y) : E.inflation e.hom := by
  apply E.inflation_of_isKernel (p := (0 : Y ⟶ 0)) (by simp) _ (E.deflation_zero Y)
  refine KernelFork.IsLimit.ofι e.hom (by simp)
    (fun g _ => g ≫ e.inv) (fun g _ => by simp) ?_
  intro W g _ m hm
  rw [← hm]
  simp

/-- Every isomorphism is an admissible epimorphism, by the dual cokernel argument. -/
lemma deflation_of_iso {X Y : C} (e : X ≅ Y) : E.deflation e.hom := by
  apply E.deflation_of_isCokernel (i := (0 : 0 ⟶ X)) (by simp) _ (E.inflation_zero X)
  refine CokernelCofork.IsColimit.ofπ e.hom (by simp)
    (fun g _ => e.inv ≫ g) (fun g _ => by simp) ?_
  intro W g _ m hm
  rw [← hm]
  simp

/-- An admissible epimorphism which is also a monomorphism is invertible. -/
lemma isIso_of_deflation_of_mono {X Y : C} (f : X ⟶ Y) [Mono f]
    (hf : E.deflation f) : IsIso f := by
  obtain ⟨K, k, hk, hc⟩ := hf
  have hz : k = 0 := (cancel_mono f).1 (by simpa using hk)
  exact CokernelCofork.IsColimit.isIso_π _ (E.cokernel _ hc) hz

end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_tag "COL-0047",
  colib_ref "BuhlerExactCategories" "Remark 2.3" "clause"
    "Isomorphisms are both admissible monomorphisms and admissible epimorphisms"]
  CategoryTheory.ExactCategory.ExactStructure.inflation_of_iso
  CategoryTheory.ExactCategory.ExactStructure.deflation_of_iso

attribute [colib_tag "COL-0047",
  colib_ref "BuhlerExactCategories" "Definition 2.1, kernel-cokernel pairs" "adaptation"
    "A monic admissible epimorphism is invertible by its cokernel universal property"]
  CategoryTheory.ExactCategory.ExactStructure.isIso_of_deflation_of_mono
