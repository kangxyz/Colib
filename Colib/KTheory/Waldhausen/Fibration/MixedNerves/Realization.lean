/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.TransposeNerves
public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.Cylinder
public import Colib.KTheory.Waldhausen.Fibration.TrivialCofibrations.Classifying
public import Colib.Topology.Realization.BisimplicialEquivalence

/-! # The original mixed weak-cofibration inclusion realizes to an equivalence

At each fine degree the actual pointwise cylinder contracts the original
comma categories, so Quillen A applies to the literal horizontal inclusion.
The checked bisimplicial theorem then gives an actual diagonal homotopy
equivalence. The exact transpose square transports it back to the original
fine-weak nerve of coarse-weak chains. The forward map is the unchanged
inclusion throughout. The topological endpoint explicitly uses a common
object/hom universe, as required by the proved Quillen-A implementation.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/Realization.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.MixedNerves
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V)
  (D : TrivialCofibrations.CylinderData V.cof N.coarse.weq)
  (hD : CylinderPreservesFineSquares N D)
  [N.coarse.weq.HasTwoOutOfThreeProperty]

/-- Actual fixed-fine-degree Quillen A for the original pointwise inclusion. -/
def horizontalClassifyingHomotopyEquiv (k : SimplexCategory) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (HorizontalCofChains N k))
      (ClassifyingSpace (HorizontalChains N k)) :=
  TrivialCofibrations.inclusionClassifyingHomotopyEquiv
    (pointwiseCof V k) (pointwiseCoarse N k) (chainCylinder N D hD k)

@[simp] theorem horizontalClassifyingHomotopyEquiv_toFun (k : SimplexCategory) :
    (horizontalClassifyingHomotopyEquiv N D hD k).toFun =
      (classifyingSpaceMap (horizontalInclusion N k)).hom :=
  TrivialCofibrations.inclusionClassifyingHomotopyEquiv_toFun _ _ _

/-- The literal transposed diagonal inclusion is a genuine realization equivalence. -/
def horizontalRealizationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |SSet.diagonalSSet (horizontalCofNerve N)|
      |SSet.diagonalSSet (horizontalNerve N)| :=
  SSet.BisimplicialRealization.diagonalRealizationHomotopyEquiv (horizontalNerveInclusion N)
    (fun k ↦ horizontalClassifyingHomotopyEquiv N D hD ⦋k⦌)
    (fun k ↦ horizontalClassifyingHomotopyEquiv_toFun N D hD ⦋k⦌)

@[simp] theorem horizontalRealizationHomotopyEquiv_toFun :
    (horizontalRealizationHomotopyEquiv N D hD).toFun =
      (SSet.toTop.map (SSet.diagonalMap (horizontalNerveInclusion N))).hom := rfl

include D hD in
/-- The exact transpose inclusion square gives the original mixed-diagonal map. -/
theorem chainInclusion_isRealizationEquivalence :
    SSet.IsRealizationEquivalence (SSet.diagonalMap (chainInclusion N)) :=
  SSet.IsRealizationEquivalence.of_iso_square _ _ (cofDiagonalIso N) (coarseDiagonalIso N)
    (diagonal_inclusion N) ⟨horizontalRealizationHomotopyEquiv N D hD, rfl⟩

/-- Actual mixed realization equivalence with the unchanged inclusion as forward map. -/
def chainInclusionRealizationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |SSet.diagonalSSet (cofChainNerve N)|
      |SSet.diagonalSSet (coarseChainNerve N)| := by
  let h := chainInclusion_isRealizationEquivalence N D hD
  let e := h.choose
  have he := h.choose_spec
  exact {
    toFun := (SSet.toTop.map (SSet.diagonalMap (chainInclusion N))).hom
    invFun := e.invFun
    left_inv := by rw [← he]; exact e.left_inv
    right_inv := by rw [← he]; exact e.right_inv }

@[simp] theorem chainInclusionRealizationHomotopyEquiv_toFun :
    (chainInclusionRealizationHomotopyEquiv N D hD).toFun =
      (SSet.toTop.map (SSet.diagonalMap (chainInclusion N))).hom := rfl

end CategoryTheory.Waldhausen.Fibration.MixedNerves
