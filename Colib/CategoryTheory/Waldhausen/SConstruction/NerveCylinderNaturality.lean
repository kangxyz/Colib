/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveCylinder

/-! # Strict reindexing of the actual nerve-direction cylinder -/
/- Implementation provenance: adapted from
   Quillen/Waldhausen/SConstruction/NerveCylinderNaturality.lean
   at c561118b7795eb9780be9ed391c3251d6a4d0afd.
   Validation status is recorded in the accompanying release report. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped Simplicial
universe v u v' u' v'' u''

namespace CategoryTheory.Waldhausen

private theorem mk₁_whiskerLeft {K : Type u} [Category.{v} K]
    {K' : Type u'} [Category.{v'} K'] {D : Type u''} [Category.{v''} D]
    (J : K' ⥤ K) {A B : K ⥤ D} (η : A ⟶ B) :
    ComposableArrows.mk₁ (whiskerLeft J η) =
      ComposableArrows.mk₁ η ⋙ (whiskeringLeft K' K D).obj J := by
  apply ComposableArrows.ext₁ (F := ComposableArrows.mk₁ (whiskerLeft J η))
    (G := ComposableArrows.mk₁ η ⋙ (whiskeringLeft K' K D).obj J) rfl rfl
  simp

variable {D : Type u} [Category.{v} D] {n m : SimplexCategory}
  {A B : Grid₂ n m ⥤ D}

/-- Independent interval and nerve reindexing commutes strictly with the actual cylinder. -/
theorem nerveCylinderDiagram_precomp (η : A ⟶ B) {n' m' : SimplexCategory}
    (α : n' ⟶ n) (β : m' ⟶ m) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram (whiskerLeft (gridMap₂ α β) η) (β ≫ τ) =
      gridMap₂ α β ⋙ nerveCylinderDiagram η τ := by
  unfold nerveCylinderDiagram
  rw [mk₁_whiskerLeft]
  rfl

/-- Equality of endpoint functors and actual transformation components gives
strict equality of the cylinders, with all type transports retained. -/
theorem nerveCylinderDiagram_congr_app {A' B' : Grid₂ n m ⥤ D}
    (η : A ⟶ B) (η' : A' ⟶ B') (hA : A = A') (hB : B = B')
    (hη : ∀ p, HEq (η.app p) (η'.app p)) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram η τ = nerveCylinderDiagram η' τ := by
  subst A'
  subst B'
  have h : η = η' := by
    ext p
    exact eq_of_heq (hη p)
  rw [h]

end CategoryTheory.Waldhausen
