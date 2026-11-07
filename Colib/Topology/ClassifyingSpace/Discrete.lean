/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Discrete
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence
public import Colib.CategoryTheory.TheoremB.TotalProjection
public import Colib.Topology.Realization.TwoSidedBar.AugmentationEquivalence

/-!
# The original classifying space of a discrete category

An actual simplicial isomorphism and the constant-realization homeomorphism
identify the original realization with the discrete object space.

Implementation provenance: `Quillen/Topology/ClassifyingSpace/Discrete.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps and universes are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology
universe u v
namespace CategoryTheory

/-- The actual nerve realization of a discrete category is the discrete object space. -/
def discreteClassifyingIso (A : Type u) :
    ClassifyingSpace (Discrete A) ≅ TopCat.discrete.obj A :=
  SSet.toTop.mapIso (SSet.TwoSidedBar.discreteNerveIso A) ≪≫ SSet.constantRealizationIso A

/-- Every positive original homotopy group of a discrete category vanishes. -/
theorem discreteClassifying_subsingleton_pi (A : Type u)
    (x : ClassifyingSpace (Discrete A)) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi (n + 1) (ClassifyingSpace (Discrete A)) x) := by
  let e := TopCat.homeoOfIso (discreteClassifyingIso A)
  let : Subsingleton (HomotopyGroup.Pi (n + 1) (TopCat.discrete.obj A)
      (e.toHomotopyEquiv.toFun x)) := HomotopyGroup.subsingleton_positive_of_discrete _ n
  exact (homotopyGroupMap_bijective_of_homotopyEquiv e.toHomotopyEquiv rfl
    (n + 1)).injective.subsingleton

end CategoryTheory
