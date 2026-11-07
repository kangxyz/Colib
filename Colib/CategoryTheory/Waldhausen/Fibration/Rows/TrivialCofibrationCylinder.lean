/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.SecondEndpoint
public import Colib.CategoryTheory.Waldhausen.Fibration.TrivialCofibrations.Category

/-! # Actual row cylinders as structural weak-cofibration comparison data

The data is supplied by the genuine exact joint cylinder, its proved target
section and its original projection. No comma or nerve comparison is assumed.


Implementation provenance:
`Quillen/Waldhausen/Fibration/Rows/TrivialCofibrationCylinder.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section



noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration
namespace RowFactorization
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : JointData N)

/-- Actual structural data for comparing original weak row cofibrations and weak row arrows. -/
def trivialCofibrationCylinder (hs : SecondEndpointSection N D) (n : SimplexCategory) :
    TrivialCofibrations.CylinderData (RowWeakEquivalences.coarseStructure N n).cof
      (RowWeakEquivalences.coarseStructure N n).weq where
  middle := middle N D n
  inclusion := inclusion N D n
  projection := projection N D n
  target := targetInclusion N D n
  factorization := (factorization N D n).factorization
  target_projection := targetInclusion_projection N D hs
  inclusion_cof := (factorization N D n).cofibration
  target_cof := targetInclusion_cof N D
  projection_weak := (factorization N D n).weak
  middle_cof α hl hr := (middle_exact N D n).cofibration α ⟨hl, hr⟩

@[simp] theorem trivialCofibrationCylinder_target (hs : SecondEndpointSection N D) (n :
    SimplexCategory) :
    (trivialCofibrationCylinder N D hs n).target = targetInclusion N D n := rfl

@[simp] theorem trivialCofibrationCylinder_projection (hs : SecondEndpointSection N D) (n :
    SimplexCategory) :
    (trivialCofibrationCylinder N D hs n).projection = (factorization N D n).projection := rfl
end RowFactorization

end CategoryTheory.Waldhausen.Fibration
