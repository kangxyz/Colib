/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.Cylinder
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.TrivialCofibrationCylinder

/-! # The original quotient-row cylinder on fine-weak chains

The genuine row middle functor preserves fine squares by its accepted
exactness. Thus the pointwise chain cylinder applies to the same original
quotient-row objects, with the original row cofibrations and coarse maps.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/RowCylinder.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section



noncomputable section
open CategoryTheory
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.MixedNerves
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : RowFactorization.JointData N)
  (hs : RowFactorization.SecondEndpointSection N D)

/-- Actual fine-square preservation of the original row cylinder. -/
theorem rowCylinder_fineSquares (n : SimplexCategory) :
    CylinderPreservesFineSquares (RowWeakEquivalences.nested N n)
      (RowFactorization.trivialCofibrationCylinder N D hs n) :=
  RowFactorization.factorization_fineSquares N D n

/-- The genuine pointwise cylinder on fine-weak chains of original quotient rows. -/
def rowChainCylinder (n k : SimplexCategory) :
    TrivialCofibrations.CylinderData
      (pointwiseCof (QuotientRows.waldhausenStructure V n) k)
      (pointwiseCoarse (RowWeakEquivalences.nested N n) k) :=
  chainCylinder (RowWeakEquivalences.nested N n)
    (RowFactorization.trivialCofibrationCylinder N D hs n) (rowCylinder_fineSquares N D hs n) k

@[simp] theorem rowChainCylinder_projection_app (n k : SimplexCategory)
    (f : Arrow (FineChain (QuotientRows.waldhausenStructure V n) k))
    (i : Fin (k.len + 1)) (p : Interval n) :
    (((rowChainCylinder N D hs n k).projection.app f).hom.app i).hom.app p =
      D.projection.app (Arrow.mk ((f.hom.hom.app i).hom.app p)) := rfl

end CategoryTheory.Waldhausen.Fibration.MixedNerves
