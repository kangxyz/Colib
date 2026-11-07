/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.SecondProjection
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/SecondProjectionFiber.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The actual strict fibers of the second-coordinate projection -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

@[simp]
theorem secondProjection_ofHom {X Y : C × D} (f : X ⟶ Y) :
    secondProjection.map (ActionLocalization.ofHom (C := C) f) =
      ActionLocalization.ofHom (C := C) f.2 :=
  ActionLocalization.mapFunctor_ofHom (CategoryTheory.Prod.snd C D) f

/-- Insert an actor object as the first coordinate in the actual strict fiber. -/
def secondFiberEntry (X : D) : C ⥤ Functor.Fiber (secondProjection (C := C)) ⟨X⟩ where
  obj A := ⟨⟨(A, X)⟩, rfl⟩
  map {A B} f := ⟨ActionLocalization.ofHom (C := C) (X := (A, X)) (Y := (B, X))
    (f, 𝟙 X), by
      have h : secondProjection.map (ActionLocalization.ofHom (C := C)
          (X := (A, X)) (Y := (B, X)) (f, 𝟙 X)) = 𝟙 (⟨X⟩ : ActionLocalization C D) := by
        rw [secondProjection_ofHom, ActionLocalization.ofHom_id]
      rw [← h]
      exact IsHomLift.map _ _⟩
  map_id A := by
    apply Subtype.ext
    exact ActionLocalization.ofHom_id (A, X)
  map_comp {A B T} f g := by
    apply Subtype.ext
    change ActionLocalization.ofHom (C := C) (X := (A, X)) (Y := (T, X)) (f ≫ g, 𝟙 X) =
      ActionLocalization.ofHom (C := C) (X := (A, X)) (Y := (B, X)) (f, 𝟙 X) ≫
        ActionLocalization.ofHom (C := C) (X := (B, X)) (Y := (T, X)) (g, 𝟙 X)
    rw [← ActionLocalization.ofHom_comp]
    simp

instance secondFiberEntry_full (X : D) [(MonoidalLeftAction.actionRight C X).Faithful] :
    (secondFiberEntry (C := C) X).Full where
  map_surjective {A B} h := by
    let := h.property
    have hh : secondProjection.map h.val =
        ActionLocalization.mkHom ⟨𝟙_ C, (λₗ[C] X).hom⟩ :=
      (IsHomLift.eq_of_isHomLift secondProjection (𝟙 (⟨X⟩ : ActionLocalization C D)) h.val).symm
    obtain ⟨k, hk, _⟩ := existsUnique_secondNormalized (X := (A, X)) (Y := (B, X))
      (𝟙_ C) (λₗ[C] X).hom h.val hh
    refine ⟨(λ_ A).inv ≫ k, ?_⟩
    apply Subtype.ext
    change mkHom (X := (A, X)) (Y := (B, X)) (𝟙_ C) ((λ_ A).hom ≫ (λ_ A).inv ≫ k)
      ((λₗ[C] X).hom ≫ 𝟙 X) = h.val
    simpa only [Iso.hom_inv_id_assoc, Category.comp_id] using hk

instance secondFiberEntry_faithful (X : D) [(MonoidalLeftAction.actionRight C X).Faithful] :
    (secondFiberEntry (C := C) X).Faithful where
  map_injective {A B} f g h := by
    have hh := congrArg Subtype.val h
    change mkHom (X := (A, X)) (Y := (B, X)) (𝟙_ C) ((λ_ A).hom ≫ f) ((λₗ[C] X).hom ≫ 𝟙 X) =
      mkHom (X := (A, X)) (Y := (B, X)) (𝟙_ C) ((λ_ A).hom ≫ g) ((λₗ[C] X).hom ≫ 𝟙 X) at hh
    simp only [Category.comp_id] at hh
    have he := (mkHom_eq_iff_same_second (X := (A, X)) (Y := (B, X))
      (𝟙_ C) (λₗ[C] X).hom _ _).1 hh
    exact (cancel_epi (λ_ A).hom).1 he

instance secondFiberEntry_essSurj (X : D) : (secondFiberEntry (C := C) X).EssSurj where
  mem_essImage Y := by
    obtain ⟨⟨⟨A, Y⟩⟩, h⟩ := Y
    have he : Y = X := congrArg ActionLocalization.obj h
    subst he
    exact ⟨A, ⟨Iso.refl _⟩⟩

instance secondFiberEntry_isEquivalence (X : D)
    [(MonoidalLeftAction.actionRight C X).Faithful] :
    (secondFiberEntry (C := C) X).IsEquivalence where

/-- The second-projection fiber is the original actor category, with its actual
arrows, under exactly the needed orbit-faithfulness hypothesis. -/
def secondFiberEquivalence (X : D) [(MonoidalLeftAction.actionRight C X).Faithful] :
    C ≌ Functor.Fiber (secondProjection (C := C)) ⟨X⟩ :=
  (secondFiberEntry (C := C) X).asEquivalence

end CategoryTheory.GroupCompletion.Localization
