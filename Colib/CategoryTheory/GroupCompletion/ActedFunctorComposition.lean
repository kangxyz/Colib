/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.ActedFunctoriality
public import Colib.CategoryTheory.Monoidal.Action.LinearComposition

/-! # Localization retains the specified composition of linear functors -/

/-!
Implementation provenance: adapted from
`Quillen/CategoryTheory/GroupCompletion/ActedFunctorComposition.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors,
comparison maps, homotopies, hypotheses and universes are retained.
-/

@[expose] public section
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open CategoryTheory.Functor.LaxLeftLinear
universe u v u₁ v₁ u₂ v₂ u₃ v₃
namespace CategoryTheory.GroupCompletion.Localization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalLeftAction C D]
  {E : Type u₂} [Category.{v₂} E] [MonoidalLeftAction C E]
  {V : Type u₃} [Category.{v₃} V] [MonoidalLeftAction C V]

/-- The localization map of the specified identity lineator is the literal identity. -/
theorem actedMapFunctor_identity :
    let := Functor.LaxLeftLinear.identity (C := C) (D := D)
    actedMapFunctor (𝟭 D) = 𝟭 (Localization C D) := by
  let := Functor.LaxLeftLinear.identity (C := C) (D := D)
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  induction h using Quotient.inductionOn with
  | h r =>
    change ActionLocalization.mkHom ⟨r.denom, (𝟙 _ ≫ r.map.1, 𝟙 _ ≫ r.map.2)⟩ =
      ActionLocalization.mkHom r
    simp only [Category.id_comp]
    rfl

/-- The actual quotient maps strictly preserve specified linear composition. -/
theorem actedMapFunctor_composition (F : D ⥤ E) (G : E ⥤ V)
    [F.LaxLeftLinear C] [G.LaxLeftLinear C] :
    let := Functor.LaxLeftLinear.composition (C := C) F G
    actedMapFunctor (C := C) (F ⋙ G) =
      actedMapFunctor (C := C) F ⋙ actedMapFunctor (C := C) G := by
  let := Functor.LaxLeftLinear.composition (C := C) F G
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  induction h using Quotient.inductionOn with
  | h r =>
    change Localization.mkHom (X := (X.obj.1, G.obj (F.obj X.obj.2)))
      (Y := (Y.obj.1, G.obj (F.obj Y.obj.2))) r.denom (𝟙 _ ≫ r.map.1)
      ((μₗ G r.denom (F.obj X.obj.2) ≫ G.map (μₗ F r.denom X.obj.2)) ≫
        G.map (F.map r.map.2)) =
      Localization.mkHom (X := (X.obj.1, G.obj (F.obj X.obj.2)))
        (Y := (Y.obj.1, G.obj (F.obj Y.obj.2))) r.denom (𝟙 _ ≫ 𝟙 _ ≫ r.map.1)
        (μₗ G r.denom (F.obj X.obj.2) ≫ G.map (μₗ F r.denom X.obj.2 ≫ F.map r.map.2))
    simp only [Category.id_comp, G.map_comp, Category.assoc]

end CategoryTheory.GroupCompletion.Localization
