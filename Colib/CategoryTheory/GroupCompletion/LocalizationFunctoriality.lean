/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.ActedFunctoriality
public import Colib.CategoryTheory.GroupCompletion.IteratedFiberEntry
public import Colib.CategoryTheory.GroupCompletion.UnitEntry

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/LocalizationFunctoriality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Equivariant functors on the original localization and its iteration -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u₁ v₁ u₂ v₂
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Functor.LaxLeftLinear
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalLeftAction C D]
  {E : Type u₂} [Category.{v₂} E] [MonoidalLeftAction C E]
  (F : D ⥤ E) [F.LaxLeftLinear C]

attribute [simp] actedMapFunctor_obj actedMapFunctor_mkHom actedMapFunctor_ofHom

@[simp]
lemma map_secondFiberHom (X : D) {A B : C} (f : A ⟶ B) :
    (actedMapFunctor F).map (secondFiberHom X f) = secondFiberHom (F.obj X) f := by
  unfold secondFiberHom
  rw [actedMapFunctor_ofHom, F.map_id]

/-- The canonical unit entry is strictly natural in the original functor. -/
lemma unitEntry_map : unitEntry (C := C) (D := D) ⋙ actedMapFunctor F = F ⋙ unitEntry := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  change (actedMapFunctor F).map (ActionLocalization.ofHom (X := (𝟙_ C, X))
    (Y := (𝟙_ C, Y)) (𝟙 _, f)) = 𝟙 _ ≫ ActionLocalization.ofHom
      (X := (𝟙_ C, F.obj X)) (Y := (𝟙_ C, F.obj Y)) (𝟙 _, F.map f) ≫ 𝟙 _
  rw [actedMapFunctor_ofHom]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

end CategoryTheory.GroupCompletion.Localization
