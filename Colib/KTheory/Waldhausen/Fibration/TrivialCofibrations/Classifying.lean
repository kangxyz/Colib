/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.TrivialCofibrations.CommaCylinder
public import Colib.CategoryTheory.TheoremA.ContractibleComma
public import Colib.Topology.ClassifyingSpace.Contraction

/-! # The original weak-cofibration inclusion is a genuine classifying equivalence

The actual comma cylinder zigzag contracts each original comma category.
The proved Quillen-A theorem then supplies a homotopy equivalence with exactly
the original inclusion's classifying map. Its topological endpoint retains
the common-universe scope of the existing Quillen-A implementation.


Implementation provenance:
`Quillen/Waldhausen/Fibration/TrivialCofibrations/Classifying.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.TrivialCofibrations
section Comma
variable {C : Type u} [Category.{v} C]
  (cof weq : MorphismProperty C) [cof.IsMultiplicative] [weq.IsMultiplicative]
  (D : CylinderData cof weq) [weq.HasTwoOutOfThreeProperty] (Y : WeakCategory weq)

/-- The original two cylinder endpoints give an actual contraction to the identity-arrow vertex. -/
def commaContraction :
    (ContinuousMap.id (ClassifyingSpace (Over cof weq Y))).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint (overPoint cof weq Y))) := by
  have h := (classifyingSpaceNaturalTransformationHomotopy (overInclusion cof weq D Y)).trans
    (classifyingSpaceNaturalTransformationHomotopy (overTarget cof weq D Y)).symm
  simpa only [classifyingSpaceMap_id, TopCat.hom_id, classifyingSpaceMap_const] using h

include D in
/-- Every genuine original weak-arrow comma category has contractible classifying space. -/
theorem comma_contractible : ContractibleSpace (ClassifyingSpace (Over cof weq Y)) := by
  apply (contractible_iff_id_nullhomotopic _).2
  exact ⟨classifyingSpacePoint (overPoint cof weq Y), ⟨commaContraction cof weq D Y⟩⟩
end Comma

section Comparison
variable {C : Type u} [SmallCategory C]
  (cof weq : MorphismProperty C) [cof.IsMultiplicative] [weq.IsMultiplicative]
  (D : CylinderData cof weq) [weq.HasTwoOutOfThreeProperty]

/-- Quillen A applied to the proved actual comma contractions and original inclusion. -/
def inclusionClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (CofibrationCategory cof weq))
      (ClassifyingSpace (WeakCategory weq)) :=
  TheoremA.contractibleCommaClassifyingHomotopyEquiv (inclusion cof weq)
    (comma_contractible cof weq D)

/-- The prescribed forward map is the unchanged inclusion of original weak cofibrations. -/
@[simp] theorem inclusionClassifyingHomotopyEquiv_toFun :
    (inclusionClassifyingHomotopyEquiv cof weq D).toFun =
      (classifyingSpaceMap (inclusion cof weq)).hom :=
  TheoremA.contractibleCommaClassifyingHomotopyEquiv_toFun _ _
end Comparison
end CategoryTheory.Waldhausen.Fibration.TrivialCofibrations
