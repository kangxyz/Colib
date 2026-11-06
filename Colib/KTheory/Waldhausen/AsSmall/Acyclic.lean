/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.AsSmall.Basic
public import Colib.CategoryTheory.Waldhausen.AsSmall.Acyclic

/-! # Original acyclic categories and extension data under the common-universe lift

Implementation provenance:
`Quillen/Waldhausen/SmallModel/Acyclic.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory Limits Opposite
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C]
namespace Fibration
variable {W : Structure C} (N : NestedWeakEquivalences W)

/-- The inherited original acyclic zero is retained by the lifted simplicial map. -/
@[simp] theorem acyclicSmallSSetIso_zero (n : SimplexCategoryᵒᵖ) :
    (acyclicSmallSSetIso N).hom.app n
      (zeroSimplex (acyclicStructure N).cof (acyclicStructure N).weq
        (acyclicStructure N).zero (acyclicStructure N).isZero n) =
      zeroSimplex (acyclicStructure N.asSmall).cof (acyclicStructure N.asSmall).weq
        (acyclicStructure N.asSmall).zero (acyclicStructure N.asSmall).isZero n := by
  apply Subtype.ext
  rfl

/-- The actual lifted acyclic realization homeomorphism. -/
def acyclicSmallDeloopingHomeomorph : (acyclicStructure N).Delooping ≃ₜ
    (acyclicStructure N.asSmall).Delooping :=
  TopCat.homeoOfIso (SSet.toTop.mapIso (acyclicSmallSSetIso N))

@[simp] theorem acyclicSmallDeloopingHomeomorph_basepoint :
    acyclicSmallDeloopingHomeomorph N (acyclicStructure N).kBasepoint =
      (acyclicStructure N.asSmall).kBasepoint := by
  change SSet.toTop.map (acyclicSmallSSetIso N).hom
    (SSet.realizationPoint (zeroSimplex _ _ _ _ (op ⦋0⦌))) = _
  rw [SSet.realizationPoint_naturality, acyclicSmallSSetIso_zero]
  rfl

end Fibration
end CategoryTheory.Waldhausen
