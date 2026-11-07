/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Monoidal.TranslationTelescopeStages
public import Colib.CategoryTheory.GroupCompletion.ActedFunctoriality
public import Colib.CategoryTheory.GroupCompletion.UnitEntry

/-! # Original completed-stage maps into localization of the telescope -/

/-!
Implementation provenance: adapted from
`Quillen/CategoryTheory/GroupCompletion/TelescopeStages.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors,
comparison maps, homotopies, hypotheses and universes are retained.
-/

@[expose] public section

open CategoryTheory.GroupCompletion

noncomputable section
open CategoryTheory MonoidalCategory Grothendieck
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
open GroupCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (e : C)
attribute [local instance] monoidalLeftAction

/-- Localize the genuine linear inclusion of the specified original stage. -/
def localizationStage (n : ℕ) : Localization C C ⥤ Localization C (Model e) :=
  Localization.actedMapFunctor (stageInclusion e n)

/-- The completed-stage map retains both original coordinates and the stage. -/
theorem localizationStage_obj (n : ℕ) (X : Localization C C) :
    (localizationStage e n).obj X = ⟨X.obj.1, (stageInclusion e n).obj X.obj.2⟩ := rfl

/-- The actual quotient representative is sent to its literal original stage arrow. -/
theorem localizationStage_mkHom (n : ℕ) {X Y : C × C} (s : C)
    (f : s ⊗ X.1 ⟶ Y.1) (g : s ⊗ X.2 ⟶ Y.2) :
    (localizationStage e n).map (Localization.mkHom s f g) =
      Localization.mkHom (X := (X.1, (stageInclusion e n).obj X.2))
        (Y := (Y.1, (stageInclusion e n).obj Y.2)) s f (stageArrow e n g) := by
  change Localization.mkHom (X := (X.1, (stageInclusion e n).obj X.2))
    (Y := (Y.1, (stageInclusion e n).obj Y.2)) s (𝟙 _ ≫ f)
      (𝟙 _ ≫ stageArrow e n g) = _
  erw [Category.id_comp, Category.id_comp]

/-- The actual unit entry commutes with every original stage inclusion. -/
theorem localizationStage_unitEntry (n : ℕ) :
    Localization.unitEntry (C := C) (D := C) ⋙ localizationStage e n =
      stageInclusion e n ⋙ Localization.unitEntry (C := C) (D := Model e) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact ActionLocalization.mapFunctor_ofHom _ _

end CategoryTheory.MonoidalCategory.TranslationTelescope
