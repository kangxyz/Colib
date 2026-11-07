/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.RowPostcompose
public import Colib.KTheory.Waldhausen.Fibration.MixedNerves.RowRealization

/-! # The original total mixed inclusion for genuine inner quotient rows

The third-index map is the original quotient-row restriction, and every
row comparison is the checked original mixed inclusion. The proved
bisimplicial realization theorem therefore totalizes these actual forward
maps. No naturality of the chosen row homotopy inverses is required.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/TotalRealization.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section



noncomputable section
open Topology
open CategoryTheory
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.MixedNerves
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : RowFactorization.JointData N)
  (hs : RowFactorization.SecondEndpointSection N D)
  [N.coarse.weq.HasTwoOutOfThreeProperty]

/-- Genuine total realization equivalence with the original three-index inclusion forward. -/
def totalChainInclusionRealizationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |SSet.diagonalSSet (cofRowDiagonals N)|
      |SSet.diagonalSSet (coarseRowDiagonals N)| :=
  SSet.BisimplicialRealization.diagonalRealizationHomotopyEquiv (rowDiagonalInclusion N)
    (fun n ↦ rowChainInclusionRealizationHomotopyEquiv N D hs ⦋n⦌)
    (fun n ↦ rowChainInclusionRealizationHomotopyEquiv_toFun N D hs ⦋n⦌)

@[simp] theorem totalChainInclusionRealizationHomotopyEquiv_toFun :
    (totalChainInclusionRealizationHomotopyEquiv N D hs).toFun =
      (SSet.toTop.map (SSet.diagonalMap (rowDiagonalInclusion N))).hom := rfl

end CategoryTheory.Waldhausen.Fibration.MixedNerves
