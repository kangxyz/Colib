/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.TelescopeInterchange

/-! # Original quotient representatives under the telescope interchange -/

/-!
Implementation provenance: adapted from
`Quillen/CategoryTheory/GroupCompletion/TelescopeInterchangeMaps.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors,
comparison maps, homotopies, hypotheses and universes are retained.
-/

@[expose] public section

open CategoryTheory.GroupCompletion

open CategoryTheory MonoidalCategory Grothendieck
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
open GroupCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (e : C)
attribute [local instance] monoidalLeftAction

/-- The interchange retains the original denominator and first-coordinate map.
The second map is the original translated stage transition followed by the
original vertical map. -/
theorem localizationInterchange_map_mkHom {n m : ℕ} (h : n ⟶ m)
    {A B X Y : C} (s : C) (f : s ⊗ A ⟶ B)
    (g : s ⊗ (EndofunctorTelescope.iterate (tensorRight e) (m - n)).obj X ⟶ Y) :
    (localizationInterchange e).map
      (show (⟨n, ⟨(A, X)⟩⟩ : Grothendieck (localizationDiagram e)) ⟶ ⟨m, ⟨(B, Y)⟩⟩ from
        ⟨h, Localization.mkHom s f g⟩) =
      Localization.mkHom (X := (A, (stageInclusion e n).obj X))
        (Y := (B, (stageInclusion e m).obj Y)) s f
        ((leftTranslation e s).map ((stageTransition e h).app X) ≫ stageArrow e m g) := by
  change (localizationStageTransition e h).app ⟨(A, X)⟩ ≫
    (localizationStage e m).map (Localization.mkHom
      (X := (A, (EndofunctorTelescope.iterate (tensorRight e) (m - n)).obj X))
      (Y := (B, Y)) s f g) = _
  rw [localizationStageTransition_app, localizationStage_mkHom]
  erw [ActionLocalization.ofHom_comp_mkHom]
  change Localization.mkHom (X := (A, (stageInclusion e n).obj X))
    (Y := (B, (stageInclusion e m).obj Y)) s (s ◁ 𝟙 A ≫ f)
      ((leftTranslation e s).map ((stageTransition e h).app X) ≫ stageArrow e m g) = _
  simp only [whiskerLeft_id, Category.id_comp]

end CategoryTheory.MonoidalCategory.TranslationTelescope
