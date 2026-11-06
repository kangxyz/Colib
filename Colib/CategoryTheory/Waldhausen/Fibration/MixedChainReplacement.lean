/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory
public import Colib.CategoryTheory.Waldhausen.Approximation.FiniteReplacement

/-! # The original cylinder replacement on mixed weak chains

The accepted functorial finite replacement is reused unchanged. Coarse-weak
arrows become coarse-weak cofibrations by its actual coarse projection and
two-out-of-three. Preservation of fine-weak natural transformations is proved
inductively from the structural fine-square preservation of the middle functor.
The projection is asserted coarse-weak only; no fine comparison or equivalence
is inferred from it.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedChainReplacement.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.FunctorialFactorization


noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.MixedChainReplacement
open FunctorialFactorization
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : FunctorialFactorization N.coarse)

/-- A structural condition on actual cylinder squares, involving only fine weak maps. -/
def PreservesFineSquares : Prop :=
  ∀ {f g : Arrow C} (α : f ⟶ g), V.weq α.left → V.weq α.right → V.weq (D.middle.map α)

/-- Every replacement stage preserves pointwise fine weak transformations. -/
theorem stage_map_fine (hD : PreservesFineSquares N D)
    {F G : ℕ ⥤ C} (α : F ⟶ G) (hα : ∀ i, V.weq (α.app i)) (i : ℕ) :
    V.weq ((stage D i).1.map α) := by
  induction i with
  | zero => exact hα 0
  | succ i hi => exact hD ((nextArrow (stage D i).1 (stage D i).2).map α) hi (hα (i+1))

/-- The unchanged sequence replacement preserves the fine class, without fine saturation. -/
theorem sequenceReplacement_map_fine (hD : PreservesFineSquares N D)
    {F G : ℕ ⥤ C} (α : F ⟶ G) (hα : ∀ i, V.weq (α.app i)) (i : ℕ) :
    V.weq (((sequenceReplacement D).map α).app i) :=
  stage_map_fine N D hD α hα i

/-- The unchanged finite replacement preserves the original pointwise fine weak maps. -/
theorem finiteReplacement_map_fine (hD : PreservesFineSquares N D) (n : ℕ)
    {F G : ComposableArrows C n} (α : F ⟶ G) (hα : ∀ i, V.weq (α.app i))
    (i : Fin (n + 1)) : V.weq (((finiteReplacement D n).map α).app i) :=
  sequenceReplacement_map_fine N D hD ((extendFinite n).map α)
    (fun k ↦ hα ((clampIndex n).obj k)) i.val

/-- All original replacement arrows are fine cofibrations because the cofibration classes agree. -/
theorem finiteReplacement_map_fine_cof (n : ℕ) (F : ComposableArrows C n)
    {i j : Fin (n + 1)} (f : i ⟶ j) : V.cof (((finiteReplacement D n).obj F).map f) := by
  rw [← N.cof_eq]
  exact finiteReplacement_map_cof D n F f

/-- The actual finite projection is coarse-weak at every original vertex. -/
theorem finiteProjection_coarse (n : ℕ) (F : ComposableArrows C n) (i : Fin (n + 1)) :
    N.coarse.weq (((finiteProjection D n).app F).app i) := finiteProjection_weak D n F i

/-- An original coarse-weak chain arrow remains coarse-weak after cylinder replacement. -/
theorem finiteReplacement_map_coarse [N.coarse.weq.HasTwoOutOfThreeProperty]
    (n : ℕ) (F : ComposableArrows C n) {i j : Fin (n + 1)} (f : i ⟶ j)
    (hf : N.coarse.weq (F.map f)) :
    N.coarse.weq (((finiteReplacement D n).obj F).map f) := by
  apply N.coarse.weq.of_postcomp _ (((finiteProjection D n).app F).app j)
    (finiteProjection_weak D n F j)
  rw [((finiteProjection D n).app F).naturality]
  exact N.coarse.weq.comp_mem _ _ (finiteProjection_weak D n F i) hf

/-- A genuine coarse-weak finite chain is resolved by genuine coarse-weak fine cofibrations. -/
theorem finiteReplacement_map_cof_coarse [N.coarse.weq.HasTwoOutOfThreeProperty]
    (n : ℕ) (F : ComposableArrows C n)
    (hF : ∀ {i j : Fin (n + 1)} (f : i ⟶ j), N.coarse.weq (F.map f))
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    V.cof (((finiteReplacement D n).obj F).map f) ∧
      N.coarse.weq (((finiteReplacement D n).obj F).map f) :=
  ⟨finiteReplacement_map_fine_cof N D n F f, finiteReplacement_map_coarse N D n F f (hF f)⟩

/-- The original first vertex is unchanged, including in outer degree zero. -/
theorem finiteReplacement_initial (n : ℕ) (F : ComposableArrows C n) :
    ((finiteReplacement D n).obj F).obj 0 = F.obj 0 := finiteReplacement_obj_zero D n F

end CategoryTheory.Waldhausen.Fibration.MixedChainReplacement
