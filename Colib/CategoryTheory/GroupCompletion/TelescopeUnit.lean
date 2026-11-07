/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.TelescopeInterchangeMaps
public import Colib.CategoryTheory.GroupCompletion.ActedUnitEntry
public import Colib.CategoryTheory.Monoidal.TranslationTelescopeFactorization

/-! # The original unit in the completed telescope model -/

/-!
Implementation provenance: adapted from `Quillen/CategoryTheory/GroupCompletion/TelescopeUnit.lean` at
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

/-- Each original right iterate commutes exactly with the original localization unit. -/
theorem unitEntry_localizationIteration (n : ℕ) :
    Localization.unitEntry (C := C) (D := C) ⋙ localizationIteration e n =
      EndofunctorTelescope.iterate (tensorRight e) n ⋙ Localization.unitEntry := by
  let := rightIterateLinear e n
  exact Localization.unitEntry_actedMapFunctor _

/-- The corresponding square retains every actual morphism, not just objects. -/
theorem localizationIteration_unitEntry_map (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (localizationIteration e n).map (Localization.unitEntry.map f) =
      (Localization.unitEntry (C := C)).map
        ((EndofunctorTelescope.iterate (tensorRight e) n).map f) :=
  eq_of_heq (CategoryTheory.Functor.hcongr_hom (unitEntry_localizationIteration e n) f)

/-- Apply the original unit to every fiber of the unwrapped right telescope. -/
def originalTelescopeUnit : EndofunctorTelescope.Model (tensorRight e) ⥤
    Grothendieck (localizationDiagram e) where
  obj X := ⟨X.base, Localization.unitEntry.obj X.fiber⟩
  map f := ⟨f.base, Localization.unitEntry.map f.fiber⟩
  map_id X := by
    refine Grothendieck.ext _ _ rfl ?_
    simp [Grothendieck.id_fiber, eqToHom_map]
  map_comp f g := by
    refine Grothendieck.ext _ _ rfl ?_
    simp only [Grothendieck.comp_fiber, Functor.map_comp, eqToHom_map]
    erw [localizationIteration_unitEntry_map]
    simp only [← Category.assoc, eqToHom_trans]
    rfl

/-- The unwrapped lift retains exactly the original unit in every fiber. -/
theorem originalTelescopeUnit_stage (n : ℕ) :
    Grothendieck.ι (EndofunctorTelescope.diagram (tensorRight e)) n ⋙
      originalTelescopeUnit e =
    Localization.unitEntry ⋙ Grothendieck.ι (localizationDiagram e) n := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Grothendieck.ext _ _ rfl ?_
  simp only [eqToHom_refl, Category.id_comp]
  change (Localization.unitEntry (C := C) (D := C)).map (eqToHom _ ≫ f) =
    eqToHom _ ≫ (Localization.unitEntry (C := C) (D := C)).map f
  rw [Functor.map_comp, eqToHom_map]

/-- The canonical original unit lift uses the prescribed common-universe telescope. -/
def telescopeUnit : Model e ⥤ Grothendieck (localizationDiagram e) :=
  (modelEquivalence e).functor ⋙ originalTelescopeUnit e

/-- The lifted unit retains every original stage. -/
theorem telescopeUnit_stage (n : ℕ) :
    stageInclusion e n ⋙ telescopeUnit e =
      Localization.unitEntry ⋙ Grothendieck.ι (localizationDiagram e) n := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Grothendieck.ext _ _ rfl ?_
  simp only [eqToHom_refl, Category.id_comp]
  change (Localization.unitEntry (C := C) (D := C)).map
      (AsSmall.down.map (eqToHom _ ≫ AsSmall.up.map f)) =
        eqToHom _ ≫ Localization.unitEntry.map f
  rw [Functor.map_comp, eqToHom_map, Functor.map_comp, eqToHom_map]
  rfl

/-- The original telescope unit is retained exactly by the interchange functor. -/
theorem telescopeUnit_interchange :
    telescopeUnit e ⋙ localizationInterchange e =
      Localization.unitEntry (C := C) (D := Model e) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (localizationStageTransition e f.base).app
      ⟨𝟙_ C, AsSmall.down.obj X.fiber⟩ ≫
        (localizationStage e Y.base).map
          ((Localization.unitEntry (C := C) (D := C)).map (AsSmall.down.map f.fiber)) =
      ActionLocalization.ofHom (𝟙 (𝟙_ C), f)
  rw [localizationStageTransition_app]
  erw [ActionLocalization.mapFunctor_ofHom]
  rw [← ActionLocalization.ofHom_comp]
  apply congrArg ActionLocalization.ofHom
  apply Prod.ext
  · exact Category.id_comp _
  · exact stageTransition_factorization e f

end CategoryTheory.MonoidalCategory.TranslationTelescope
