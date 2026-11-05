/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Bisimplicial
public import Mathlib.CategoryTheory.Functor.Currying

/-! # The genuine nerve-direction cylinder of weak natural transformations

A pointwise weak natural transformation between two genuine two-degree
S-grids can be evaluated along an ordinal map to [1]. Every individual
S-row remains an original row of one endpoint, while crossing weak arrows
use the actual component of the transformation.
-/
/- Implementation provenance: adapted from
   Quillen/Waldhausen/SConstruction/NerveCylinder.lean
   at c561118b7795eb9780be9ed391c3251d6a4d0afd.
   Validation status is recorded in the accompanying release report. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen

/-- The interval parameter only sees the nerve coordinate of the grid. -/
def nerveTimeFunctor (n : SimplexCategory) {m : SimplexCategory} (τ : m ⟶ ⦋1⦌) :
    Grid₂ n m ⥤ Fin 2 :=
  (show Monotone (fun p : Grid₂ n m ↦ τ.toOrderHom p.1) from
    fun _ _ h ↦ τ.toOrderHom.monotone h.1).functor

variable {D : Type u} [Category.{v} D] {n m : SimplexCategory}
  {A B : Grid₂ n m ⥤ D}

/-- Evaluate the actual categorical natural-transformation cylinder at the
chosen nerve time and the unchanged grid point. -/
def nerveCylinderDiagram (η : A ⟶ B) (τ : m ⟶ ⦋1⦌) : Grid₂ n m ⥤ D :=
  ((nerveTimeFunctor n τ).prod' (𝟭 (Grid₂ n m))) ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ η)

@[simp] theorem nerveCylinderDiagram_zero (η : A ⟶ B) :
    nerveCylinderDiagram η (SimplexCategory.const m ⦋1⦌ 0) = A := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro p q f
  simp [nerveCylinderDiagram, nerveTimeFunctor, Functor.uncurry, Functor.prod',
    ComposableArrows.mk₁, SimplexCategory.const]

@[simp] theorem nerveCylinderDiagram_one (η : A ⟶ B) :
    nerveCylinderDiagram η (SimplexCategory.const m ⦋1⦌ 1) = B := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro p q f
  simp [nerveCylinderDiagram, nerveTimeFunctor, Functor.uncurry, Functor.prod',
    ComposableArrows.mk₁, SimplexCategory.const]

/-- Along one S-row the time is fixed, so its map is an unchanged endpoint map. -/
theorem nerveCylinderDiagram_rowMap (η : A ⟶ B) (τ : m ⟶ ⦋1⦌)
    (t : Fin (m.len + 1)) (i j k l : Fin (n.len + 1)) (hij : i ≤ j) (hkl : k ≤ l)
    (f : grid₂ t i j hij ⟶ grid₂ t k l hkl) :
    (nerveCylinderDiagram η τ).map f =
      ((ComposableArrows.mk₁ η).obj (τ.toOrderHom t)).map f := by
  change ((ComposableArrows.mk₁ η).map (𝟙 (τ.toOrderHom t))).app (grid₂ t i j hij) ≫
    ((ComposableArrows.mk₁ η).obj (τ.toOrderHom t)).map f = _
  rw [CategoryTheory.Functor.map_id]
  simp only [NatTrans.id_app, Category.id_comp]

private theorem selected_isSimplex₂ (W : Structure D) (η : A ⟶ B)
    (hA : IsSimplex₂ W.cof W.weq A) (hB : IsSimplex₂ W.cof W.weq B) (a : Fin 2) :
    IsSimplex₂ W.cof W.weq ((ComposableArrows.mk₁ η).obj a) := by
  fin_cases a
  · exact hA
  · exact hB

private theorem cylinder_map_weak (W : Structure D) (η : A ⟶ B)
    {p q : Grid₂ n m} (f : p ⟶ q) (ha : W.weq (A.map f)) (hb : W.weq (B.map f))
    (hη : W.weq (η.app p)) (a b : Fin 2) (hab : a ≤ b) :
    W.weq (((ComposableArrows.mk₁ η).map (homOfLE hab)).app p ≫
      ((ComposableArrows.mk₁ η).obj b).map f) := by
  fin_cases a <;> fin_cases b
  · simpa using ha
  · exact W.weq.comp_mem _ _ hη hb
  · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hab)
  · simpa using hb

/-- The actual cylinder remains a genuine S-grid. Only its natural
transformation components are assumed weak, not invertible. -/
theorem nerveCylinderDiagram_isSimplex₂ (W : Structure D) (η : A ⟶ B)
    (hη : ∀ p, W.weq (η.app p)) (hA : IsSimplex₂ W.cof W.weq A)
    (hB : IsSimplex₂ W.cof W.weq B) (τ : m ⟶ ⦋1⦌) :
    IsSimplex₂ W.cof W.weq (nerveCylinderDiagram η τ) where
  zero t i := (selected_isSimplex₂ W η hA hB (τ.toOrderHom t)).zero t i
  cofibration t i j k hij hjk := by
    simp only [nerveCylinderDiagram_rowMap]
    exact (selected_isSimplex₂ W η hA hB (τ.toOrderHom t)).cofibration t i j k hij hjk
  quotient t i j k hij hjk := by
    simp only [nerveCylinderDiagram_rowMap]
    exact (selected_isSimplex₂ W η hA hB (τ.toOrderHom t)).quotient t i j k hij hjk
  weak s t i j hst hij :=
    cylinder_map_weak W η _ (hA.weak s t i j hst hij) (hB.weak s t i j hst hij)
      (hη (grid₂ s i j hij)) (τ.toOrderHom s) (τ.toOrderHom t) (τ.toOrderHom.monotone hst)

end CategoryTheory.Waldhausen
