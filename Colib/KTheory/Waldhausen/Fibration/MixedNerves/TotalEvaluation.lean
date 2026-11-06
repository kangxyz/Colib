/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.ChainEvaluation
public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.CoarseRows
public import Colib.KTheory.Waldhausen.Fibration.MixedNerves.TotalRealization

/-! # The prescribed total mixed evaluation into the original coarse S-construction

Actual rowwise diagonal evaluation is natural for the unchanged row
restriction. The proved rowwise-diagonal theorem gives its prescribed total
homotopy equivalence. The genuine coarse-row presentation then identifies the
target with the original coarse Waldhausen simplicial set. The cofibration
version uses the separately proved actual cylinder-based inclusion theorem.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/TotalEvaluation.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.MixedNerves
section Coarse
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- Original diagonal evaluation, natural in the actual inner row degree. -/
def coarseRowEvaluation : coarseRowDiagonals N ⟶ coarseWeakRowNerve N where
  app m := coarseChainEvaluation.{u,v} (RowWeakEquivalences.nested N m.unop)
  naturality _ _ α := coarseChainEvaluation_naturality.{u,v} (rowReindexCompatible N α.unop)

@[simp] theorem coarseRowEvaluation_app (m : SimplexCategory) :
    (coarseRowEvaluation N).app (op m) = coarseChainEvaluation (RowWeakEquivalences.nested N m)
      := rfl

/-- The actual coarse-row target is retained while taking the final diagonal. -/
def coarseRowEvaluationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |SSet.diagonalSSet (coarseRowDiagonals N)|
      |SSet.diagonalSSet (coarseWeakRowNerve N)| :=
  SSet.BisimplicialRealization.diagonalRealizationHomotopyEquiv (coarseRowEvaluation N)
    (fun m ↦ coarseChainEvaluationHomotopyEquiv.{u,v} (RowWeakEquivalences.nested N ⦋m⦌))
    (fun m ↦ coarseChainEvaluationHomotopyEquiv_toFun.{u,v} (RowWeakEquivalences.nested N ⦋m⦌))

@[simp] theorem coarseRowEvaluationHomotopyEquiv_toFun :
    (coarseRowEvaluationHomotopyEquiv N).toFun =
      (SSet.toTop.map (SSet.diagonalMap (coarseRowEvaluation N))).hom := rfl

/-- The prescribed map into the original coarse S-construction uses only its proved row
presentation. -/
def totalCoarseEvaluation : SSet.diagonalSSet (coarseRowDiagonals N) ⟶
    sSet N.coarse.cof N.coarse.weq :=
  SSet.diagonalMap (coarseRowEvaluation N) ≫ (coarseSSetIso N).hom

/-- Genuine realization equivalence with exactly the original coarse S-set as target. -/
def totalCoarseEvaluationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |SSet.diagonalSSet (coarseRowDiagonals N)|
      |sSet N.coarse.cof N.coarse.weq| :=
  (coarseRowEvaluationHomotopyEquiv N).trans
    (TopCat.homeoOfIso (SSet.toTop.mapIso (coarseSSetIso N))).toHomotopyEquiv

@[simp] theorem totalCoarseEvaluationHomotopyEquiv_toFun :
    (totalCoarseEvaluationHomotopyEquiv N).toFun =
      (SSet.toTop.map (totalCoarseEvaluation N)).hom := by
  simp only [totalCoarseEvaluationHomotopyEquiv, totalCoarseEvaluation, Functor.map_comp]
  rfl

/-- The original cofibration-chain augmentation retains the same exact coarse-row target. -/
def cofRowEvaluation : cofRowDiagonals N ⟶ coarseWeakRowNerve N :=
  rowDiagonalInclusion N ≫ coarseRowEvaluation N

/-- The prescribed original cofibration-chain total augmentation. -/
def totalCofEvaluation : SSet.diagonalSSet (cofRowDiagonals N) ⟶
    sSet N.coarse.cof N.coarse.weq :=
  SSet.diagonalMap (cofRowEvaluation N) ≫ (coarseSSetIso N).hom

/-- This is literally the original mixed inclusion followed by the proved coarse augmentation. -/
theorem totalCofEvaluation_eq : totalCofEvaluation N =
    SSet.diagonalMap (rowDiagonalInclusion N) ≫ totalCoarseEvaluation N := rfl
end Coarse

section Cofibration
-- The cylinder-based Quillen-A comparison currently has this explicit common-universe scope.
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : RowFactorization.JointData N)
  (hs : RowFactorization.SecondEndpointSection N D)
  [N.coarse.weq.HasTwoOutOfThreeProperty]

/-- The genuine original-cylinder inclusion theorem gives the cofibration-total evaluation
equivalence. -/
def totalCofEvaluationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |SSet.diagonalSSet (cofRowDiagonals N)|
      |sSet N.coarse.cof N.coarse.weq| :=
  (totalChainInclusionRealizationHomotopyEquiv N D hs).trans
    (totalCoarseEvaluationHomotopyEquiv N)

@[simp] theorem totalCofEvaluationHomotopyEquiv_toFun :
    (totalCofEvaluationHomotopyEquiv N D hs).toFun =
      (SSet.toTop.map (totalCofEvaluation N)).hom := by
  change (totalCoarseEvaluationHomotopyEquiv N).toFun.comp
    (totalChainInclusionRealizationHomotopyEquiv N D hs).toFun = _
  rw [totalCoarseEvaluationHomotopyEquiv_toFun,
    totalChainInclusionRealizationHomotopyEquiv_toFun,
    totalCofEvaluation_eq, SSet.toTop.map_comp, TopCat.hom_comp]
end Cofibration
end CategoryTheory.Waldhausen.Fibration.MixedNerves
