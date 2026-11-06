/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.Restriction
public import Colib.Topology.HomotopyPullback.RetractionBaseChange

/-!
# Retractions of path-space homotopy pullbacks

A retraction comparison gives the stated homotopy equivalence of actual path-space homotopy
    pullbacks.
-/
/-! Implementation source: `Quillen/Topology/HomotopyPullback/Retraction.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual path-space comparisons and
pushout hypotheses are retained. -/
@[expose] public section


noncomputable section
open Topology TopCat
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.HomotopyPullback

variable {E D T B : TopCat.{u}} (q : E ⟶ T) (p : D ⟶ T) (S : Set D)
  {i : B ⟶ TopCat.of S} (R : TopCat.CylinderStrongDeformationRetract i)
  (hR : R.H ≫ R.r = fst (TopCat.of S) TopCat.I ≫ R.r)
  (b : B ⟶ T) (hr : restrictedParameter p.hom S = b.hom.comp R.r.hom)

/-- In retraction coordinates, the endpoint homotopy pullback is homotopy
 equivalent to the entire restricted homotopy pullback. -/
def restrictionRetractionHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (HomotopyPullback q.hom b.hom)
      {z : HomotopyPullback q.hom p.hom // baseProjection q.hom p.hom z ∈ S} :=
  (RetractionPullback.homotopyEquiv R
    (TopCat.ofHom (baseProjection q.hom b.hom)) hR).trans
      (retractionChartHomeomorph q.hom p.hom S R.r.hom b.hom hr).symm.toHomotopyEquiv

@[simp] theorem restrictionRetractionHomotopyEquiv_apply
    (z : HomotopyPullback q.hom b.hom) :
    ((restrictionRetractionHomotopyEquiv q p S R hR b hr).toFun z).1.1 =
      ((i z.1.1).1, z.1.2) := rfl

end Topology.HomotopyPullback

end
