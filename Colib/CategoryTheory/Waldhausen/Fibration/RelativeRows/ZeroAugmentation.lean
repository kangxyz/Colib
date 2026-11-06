/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.Index
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.IsomorphicSources
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-! # Adjoining the actual chosen zero to a finite chain

The original positive-index objects and maps are unchanged. The new maps
from the initial object are the actual maps from the chosen Waldhausen zero.
This is an actual functor on all natural transformations of finite chains.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/ZeroAugmentation.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The chosen zero followed by all original chain objects. -/
def zeroAugmentObj {n : ℕ} (F : ComposableArrows C n) : Fin (n + 2) → C := Fin.cases W.zero F.obj

/-- The original positive-index maps and the unique original maps from zero. -/
def zeroAugmentMap {n : ℕ} (F : ComposableArrows C n)
    (i j : Fin (n + 2)) (h : i ≤ j) : zeroAugmentObj W F i ⟶ zeroAugmentObj W F j := by
  cases i using Fin.cases with
  | zero => exact W.isZero.to_ _
  | succ i =>
    cases j using Fin.cases with
    | zero => have hi : i.val + 1 ≤ 0 := h; omega
    | succ j => exact F.map (homOfLE (Nat.le_of_succ_le_succ h))

/-- The actual zero-start augmentation of a finite chain. -/
def zeroAugment {n : ℕ} (F : ComposableArrows C n) : ComposableArrows C (n + 1) where
  obj := zeroAugmentObj W F
  map f := zeroAugmentMap W F _ _ (leOfHom f)
  map_id i := by
    cases i using Fin.cases with
    | zero => exact W.isZero.eq_of_src _ _
    | succ i => exact F.map_id i
  map_comp {i j k} f g := by
    cases i using Fin.cases with
    | zero => exact W.isZero.eq_of_src _ _
    | succ i =>
      cases j using Fin.cases with
      | zero => have hi : i.val + 1 ≤ 0 := leOfHom f; omega
      | succ j =>
        cases k using Fin.cases with
        | zero => have hj : j.val + 1 ≤ 0 := leOfHom g; omega
        | succ k => exact F.map_comp _ _

@[simp] theorem zeroAugment_obj_zero {n : ℕ} (F : ComposableArrows C n) :
    (zeroAugment W F).obj 0 = W.zero := rfl
@[simp] theorem zeroAugment_obj_succ {n : ℕ} (F : ComposableArrows C n) (i : Fin (n + 1)) :
    (zeroAugment W F).obj i.succ = F.obj i := rfl

@[simp] theorem zeroAugment_map_succ {n : ℕ} (F : ComposableArrows C n)
    {i j : Fin (n + 1)} (h : i ≤ j) :
    (zeroAugment W F).map (homOfLE (show i.succ ≤ j.succ from Nat.succ_le_succ h)) =
      F.map (homOfLE h) := rfl

/-- Augment an original natural transformation by the identity of the chosen zero. -/
def zeroAugmentNatTrans {n : ℕ} {F G : ComposableArrows C n} (α : F ⟶ G) :
    zeroAugment W F ⟶ zeroAugment W G where
  app i := by
    cases i using Fin.cases with
    | zero => exact 𝟙 W.zero
    | succ i => exact α.app i
  naturality i j f := by
    cases i using Fin.cases with
    | zero => exact W.isZero.eq_of_src _ _
    | succ i =>
      cases j using Fin.cases with
      | zero => have hi : i.val + 1 ≤ 0 := leOfHom f; omega
      | succ j => exact α.naturality _

/-- Zero augmentation is genuinely functorial on every original chain map. -/
def zeroAugmentFunctor (n : ℕ) : ComposableArrows C n ⥤ ComposableArrows C (n + 1) where
  obj := zeroAugment W
  map := zeroAugmentNatTrans W
  map_id F := by ext i; cases i using Fin.cases <;> rfl
  map_comp α β := by
    ext i
    cases i using Fin.cases with
    | zero => exact (Category.id_comp _).symm
    | succ i => rfl

@[simp] theorem zeroAugmentNatTrans_app_succ {n : ℕ} {F G : ComposableArrows C n}
    (α : F ⟶ G) (i : Fin (n + 1)) : (zeroAugmentNatTrans W α).app i.succ = α.app i := rfl

/-- Actual cofibration chains remain actual cofibration chains after zero augmentation. -/
theorem zeroAugment_map_cof {n : ℕ} (F : ComposableArrows C n)
    (hF : ∀ {i j : Fin (n + 1)} (f : i ⟶ j), W.cof (F.map f))
    {i j : Fin (n + 2)} (f : i ⟶ j) : W.cof ((zeroAugment W F).map f) := by
  cases i using Fin.cases with
  | zero => exact W.cof_zero _
  | succ i =>
    cases j using Fin.cases with
    | zero => have hi : i.val + 1 ≤ 0 := leOfHom f; omega
    | succ j => exact hF _

/-- The original pointwise weak maps remain weak, with identity at the added zero. -/
theorem zeroAugmentNatTrans_weak {n : ℕ} {F G : ComposableArrows C n} (α : F ⟶ G)
    (hα : ∀ i, W.weq (α.app i)) (i : Fin (n + 2)) : W.weq ((zeroAugmentNatTrans W α).app i) := by
  cases i using Fin.cases with
  | zero => exact W.weq.id_mem _
  | succ i => exact hα i

/-- Include the unchanged original positive indices. -/
def successorIndex (n : ℕ) : Fin (n + 1) ⥤ Fin (n + 2) :=
  (show Monotone (fun i : Fin (n + 1) ↦ i.succ) from fun _ _ h ↦ Nat.succ_le_succ h).functor

/-- Removing the newly adjoined zero recovers the original chain strictly. -/
@[simp] theorem successorIndex_zeroAugment {n : ℕ} (F : ComposableArrows C n) :
    successorIndex n ⋙ zeroAugment W F = F := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.Fibration.RelativeRows
