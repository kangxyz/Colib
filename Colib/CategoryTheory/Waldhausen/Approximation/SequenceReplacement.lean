/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.FunctorialFactorization.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Functorial cofibration replacement of sequences

Iterated actual functorial factorization replaces any sequence by a
sequence of cofibrations. The comparison to the original sequence is
natural in the whole sequence, objectwise a weak equivalence, and the
initial object is unchanged. No comparison equivalence is assumed.


Implementation provenance:
`Quillen/Waldhausen/Approximation/SequenceReplacement.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Waldhausen.FunctorialFactorization

variable {C : Type u} [Category.{v} C] {W : Structure C}

/-- The map to the next input vertex, naturally in the entire input sequence. -/
def nextArrow {n : ℕ} (G : (ℕ ⥤ C) ⥤ C)
    (q : G ⟶ (evaluation ℕ C).obj n) : (ℕ ⥤ C) ⥤ Arrow C where
  obj F := Arrow.mk (q.app F ≫ F.map (homOfLE (Nat.le_add_right n 1)))
  map {F F'} α := Arrow.homMk (G.map α) (α.app (n + 1)) (by
    dsimp
    rw [← Category.assoc, q.naturality]
    change (q.app F ≫ α.app n) ≫ F'.map _ = _
    rw [Category.assoc, ← α.naturality, ← Category.assoc])
  map_id _ := by apply Arrow.hom_ext <;> simp
  map_comp _ _ := by apply Arrow.hom_ext <;> simp

/-- The n-th replacement vertex and its coherent comparison to the input vertex. -/
def stage (D : FunctorialFactorization W) :
    (n : ℕ) → Σ G : (ℕ ⥤ C) ⥤ C, G ⟶ (evaluation ℕ C).obj n
  | 0 => ⟨(evaluation ℕ C).obj 0, 𝟙 _⟩
  | n + 1 => ⟨nextArrow (stage D n).1 (stage D n).2 ⋙ D.middle, {
      app F := D.projection.app ((nextArrow (stage D n).1 (stage D n).2).obj F)
      naturality _ _ α := D.projection.naturality
        ((nextArrow (stage D n).1 (stage D n).2).map α) }⟩

/-- The successive replacement arrows are naturally chosen cofibrations. -/
def stageStep (D : FunctorialFactorization W) (n : ℕ) :
    (stage D n).1 ⟶ (stage D (n + 1)).1 where
  app F := D.inclusion.app ((nextArrow (stage D n).1 (stage D n).2).obj F)
  naturality _ _ α := D.inclusion.naturality
    ((nextArrow (stage D n).1 (stage D n).2).map α)

/-- The comparison squares commute as actual arrows. -/
theorem stageStep_projection (D : FunctorialFactorization W) (n : ℕ) (F : ℕ ⥤ C) :
    (stageStep D n).app F ≫ (stage D (n + 1)).2.app F =
      (stage D n).2.app F ≫ F.map (homOfLE (Nat.le_add_right n 1)) :=
  D.factorization _

/-- The replacement of sequences is a genuine functor. -/
def sequenceReplacement (D : FunctorialFactorization W) : (ℕ ⥤ C) ⥤ (ℕ ⥤ C) :=
  (Functor.ofSequence (stageStep D)).flip

@[simp]
theorem sequenceReplacement_obj_zero (D : FunctorialFactorization W) (F : ℕ ⥤ C) :
    ((sequenceReplacement D).obj F).obj 0 = F.obj 0 := rfl

/-- The coherent comparison to the original sequence. -/
def sequenceProjection (D : FunctorialFactorization W) : sequenceReplacement D ⟶ 𝟭 _ where
  app F := NatTrans.ofSequence (fun n ↦ (stage D n).2.app F) (by
    intro n
    change ((Functor.ofSequence (stageStep D)).map _).app F ≫ _ = _
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact stageStep_projection D n F)
  naturality F G α := by
    ext n
    exact (stage D n).2.naturality α

/-- Every vertex of the comparison is an actual weak equivalence. -/
theorem sequenceProjection_weak (D : FunctorialFactorization W) (F : ℕ ⥤ C) (n : ℕ) :
    W.weq ((sequenceProjection D).app F |>.app n) := by
  cases n with
  | zero => exact W.weq.id_mem _
  | succ n => exact D.weak _

/-- Each successive replacement arrow is a cofibration. -/
theorem sequenceReplacement_step_cof (D : FunctorialFactorization W) (F : ℕ ⥤ C) (n : ℕ) :
    W.cof (((sequenceReplacement D).obj F).map (homOfLE (Nat.le_add_right n 1))) := by
  change W.cof (((Functor.ofSequence (stageStep D)).map _).app F)
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact D.cofibration _

/-- Hence every forward arrow in the replacement sequence is a cofibration. -/
theorem sequenceReplacement_map_cof (D : FunctorialFactorization W) (F : ℕ ⥤ C)
    {i j : ℕ} (f : i ⟶ j) : W.cof (((sequenceReplacement D).obj F).map f) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom f)
  obtain rfl := Subsingleton.elim f (homOfLE (Nat.le_add_right i k))
  induction k with
  | zero => simpa using W.cof.id_mem (((sequenceReplacement D).obj F).obj i)
  | succ k ih =>
    have h : homOfLE (Nat.le_add_right i (k + 1)) =
        homOfLE (Nat.le_add_right i k) ≫ homOfLE (Nat.le_add_right (i + k) 1) := rfl
    rw [h, Functor.map_comp]
    exact W.cof.comp_mem _ _ ih (sequenceReplacement_step_cof D F (i + k))

/-- Under saturation, pointwise weak equivalences of input sequences induce
pointwise weak equivalences of their replacements. -/
theorem sequenceReplacement_map_weak (D : FunctorialFactorization W)
    [W.weq.HasTwoOutOfThreeProperty] {F G : ℕ ⥤ C} (α : F ⟶ G)
    (hα : ∀ n, W.weq (α.app n)) (n : ℕ) :
    W.weq (((sequenceReplacement D).map α).app n) := by
  apply W.weq.of_postcomp _ ((sequenceProjection D).app G |>.app n)
    (sequenceProjection_weak D G n)
  rw [← NatTrans.comp_app, (sequenceProjection D).naturality, NatTrans.comp_app]
  exact W.weq.comp_mem _ _ (sequenceProjection_weak D F n) (hα n)

end CategoryTheory.Waldhausen.FunctorialFactorization
