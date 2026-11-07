/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.ConstantChains
public import Colib.Topology.Realization.BisimplicialEquivalence
public import Colib.CategoryTheory.TheoremA.Augmentations

/-! # The prescribed constant-chain map on the actual mixed diagonal

The original forward nerve maps are ordinal-natural; their actual rowwise
homotopy equivalences imply the diagonal comparison through the accepted
rowwise-diagonal theorem. No ordinal-natural evaluation inverse is required.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/ConstantDiagonal.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.MixedNerves
variable {C : Type (max u v)} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The original constant-chain map, with only the canonical constant-diagonal identification. -/
def constantHorizontalDiagonalMap : nerve (TrivialCofibrations.WeakCategory N.coarse.weq) ⟶
    SSet.diagonalSSet (horizontalNerve N) :=
  (CategoryTheory.TheoremA.diagonalConstantIso _).inv ≫ SSet.diagonalMap (constantHorizontalNerve N)

/-- The actual rowwise constant-chain homotopy equivalences induce a genuine diagonal
equivalence. -/
def constantHorizontalDiagonalHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (TrivialCofibrations.WeakCategory N.coarse.weq))
      |SSet.diagonalSSet (horizontalNerve N)| :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (CategoryTheory.TheoremA.diagonalConstantIso
    _).symm)).toHomotopyEquiv.trans
    (SSet.BisimplicialRealization.diagonalRealizationHomotopyEquiv (constantHorizontalNerve N)
      (fun n ↦ constantHorizontalClassifyingHomotopyEquiv N (SimplexCategory.mk n)) (fun _ ↦ rfl))

/-- The prescribed forward map is exactly the original constant-chain diagonal map. -/
@[simp] theorem constantHorizontalDiagonalHomotopyEquiv_toFun :
    (constantHorizontalDiagonalHomotopyEquiv N).toFun =
      (SSet.toTop.map (constantHorizontalDiagonalMap N)).hom := by
  simp only [constantHorizontalDiagonalHomotopyEquiv, constantHorizontalDiagonalMap,
    Functor.map_comp]
  rfl

end CategoryTheory.Waldhausen.Fibration.MixedNerves
