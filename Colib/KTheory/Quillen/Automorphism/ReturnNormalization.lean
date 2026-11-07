/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.SourceContraction
public import Colib.Topology.Homotopy.ConcatenationFamilies
public import Colib.KTheory.Quillen.Automorphism.PositiveNormalization

/-!
Implementation provenance: `Quillen/KTheory/Automorphism/ReturnNormalization.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, tracks,
hypotheses, and signs are retained under native mathematical ownership.

# The original fiber inverse and actual return-path normalization

The displayed source contraction and supplied return path give a genuine
homotopy from the unchanged reversed loop-fiber inverse to right normalization.
The native finite-stage comparison consumes this construction with its actual
stored quotient path and actual denominator endpoint path.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
open Topology HomotopyGroup CategoryTheory.ExactCategory
open scoped Topology unitInterval
namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (f : C(X, Y)) (y : Y) (h : C(Z, HomotopyFiber f y)) (e : X)
  (H : ((projection f y).comp h).Homotopy (ContinuousMap.const Z e))
  (γ : Path (f e) y)

/-- Reverse the actual contracted fiber path and append the supplied return path. -/
def contractionReturnLoop : C(Z, Path y y) where
  toFun z := (contractedPathMap f y h e H z).symm.trans γ
  continuous_toFun := (Path.continuous_symm.comp
    (contractedPathMap f y h e H).continuous).path_trans continuous_const

/-- The reversed contracted paths form a genuine homotopy between their fixed endpoints. -/
def reverseContractedPathHomotopy :
    (ContinuousMap.const Z y).Homotopy (ContinuousMap.const Z (f e)) where
  toFun z := (contractedPathMap f y h e H z.2).symm z.1
  continuous_toFun := continuous_eval.comp
    ((Path.continuous_symm.comp
      ((contractedPathMap f y h e H).continuous.comp continuous_snd)).prodMk continuous_fst)
  map_zero_left z := (contractedPathMap f y h e H z).symm.source
  map_one_left z := (contractedPathMap f y h e H z).symm.target

/-- The supplied return path cancels through the actual common-tail homotopy. -/
def returnNormalizationHomotopy (z₀ : Z) :
    (Automorphism.rightNormalizedLoopMap (contractionReturnLoop f y h e H γ) z₀).Homotopy
      (loopReversal.comp (contractedDifference f y h e H z₀)) := by
  let a := contractedPathMap f y h e H
  let A := reverseContractedPathHomotopy f y h e H
  let B : (ContinuousMap.const Z y).Homotopy (ContinuousMap.const Z (f e)) :=
    (a z₀).symm.toHomotopyConst
  let G : (ContinuousMap.const Z (f e)).Homotopy (ContinuousMap.const Z y) :=
    γ.toHomotopyConst
  have J := ConePair.commonTailCancellation A B G
  refine J.cast ?_ ?_
  · ext z t
    change (((A.trans G).evalAt z).trans ((B.trans G).evalAt z).symm) t = _
    rw [ConePair.evalAt_trans, ConePair.evalAt_trans]
    rfl
  · ext z t
    change ((a z).symm.trans (a z₀).symm.symm) t = ((a z₀).symm.trans (a z)).symm t
    rw [Path.trans_symm]

/-- The unchanged reversed loop-fiber inverse is homotopic to the displayed right normalization. -/
def inverseReturnNormalizationHomotopy [ContractibleSpace X] (z₀ : Z) :
    (loopReversal.comp
      (((loopEquivOfContractibleSourcePath f (h z₀).val.1 y
        (toPath f y (h z₀))).invFun).comp h)).Homotopy
      (Automorphism.rightNormalizedLoopMap (contractionReturnLoop f y h e H γ) z₀) :=
  ((ContinuousMap.Homotopy.refl loopReversal).comp
    (inverseContractionHomotopy f y h e H z₀)).trans
      (returnNormalizationHomotopy f y h e H γ z₀).symm

end Topology.HomotopyFiber

namespace CategoryTheory.ExactCategory.Automorphism
/-- A genuine map homotopy right-normalizes continuously along its own basepoint track. -/
def rightNormalizedHomotopy {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {x : X}
    {f g : C(Z, Path x x)} (H : f.Homotopy g) (z₀ : Z) :
    (Automorphism.rightNormalizedLoopMap f z₀).Homotopy
      (Automorphism.rightNormalizedLoopMap g z₀) where
  toFun z := (H z).trans (H (z.1,z₀)).symm
  continuous_toFun := H.continuous.path_trans
    (Path.continuous_symm.comp (H.continuous.comp (continuous_fst.prodMk continuous_const)))
  map_zero_left z := by
    change (H (0, z)).trans (H (0, z₀)).symm = _
    rw [H.apply_zero, H.apply_zero]
    rfl
  map_one_left z := by
    change (H (1, z)).trans (H (1, z₀)).symm = _
    rw [H.apply_one, H.apply_one]
    rfl


end CategoryTheory.ExactCategory.Automorphism
