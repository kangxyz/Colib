/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.RowCylinder
public import Colib.KTheory.Waldhausen.Fibration.MixedNerves.Realization

/-! # The original mixed inclusion for genuine quotient-row cylinders

The base structural inputs are supplied by the accepted row cylinder. The
concrete complex specialization retains the original mixed nerve maps and
requires the stated cone and shift closure, with no kernel closure. As with
the generic realized theorem, object and hom universes agree here.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/RowRealization.lean`
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

/-- The unchanged original mixed row inclusion is a genuine realization homotopy equivalence. -/
def rowChainInclusionRealizationHomotopyEquiv (n : SimplexCategory) :
    ContinuousMap.HomotopyEquiv
      |SSet.diagonalSSet (cofChainNerve (RowWeakEquivalences.nested N n))|
      |SSet.diagonalSSet (coarseChainNerve (RowWeakEquivalences.nested N n))| := by
  letI : (RowWeakEquivalences.nested N n).coarse.weq.HasTwoOutOfThreeProperty :=
    RowWeakEquivalences.coarseStructure_twoOutOfThree N n
  exact chainInclusionRealizationHomotopyEquiv (RowWeakEquivalences.nested N n)
    (RowFactorization.trivialCofibrationCylinder N D hs n) (rowCylinder_fineSquares N D hs n)

@[simp] theorem rowChainInclusionRealizationHomotopyEquiv_toFun (n : SimplexCategory) :
    (rowChainInclusionRealizationHomotopyEquiv N D hs n).toFun =
      (SSet.toTop.map (SSet.diagonalMap (chainInclusion (RowWeakEquivalences.nested N
        n)))).hom := rfl

end CategoryTheory.Waldhausen.Fibration.MixedNerves
