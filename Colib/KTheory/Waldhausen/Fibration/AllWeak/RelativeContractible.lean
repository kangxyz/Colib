/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Fibration.AllWeak.CoproductCylinder
public import Colib.KTheory.Waldhausen.Fibration.RelativeRows.CoarseEvaluation

/-! # Contractibility of the actual identity-relative total S-model

Every object is acyclic in the all-weak coarse structure. The previously
proved original relative evaluation, with the genuine coproduct cylinder,
identifies this actual relative total with the contracted all-weak
S-realization. This establishes contractibility only; no double-S loop or
homotopy-fiber comparison is assumed or asserted.


Implementation provenance:
`Quillen/Waldhausen/Fibration/AllWeak/RelativeContractible.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory
open scoped Simplicial Topology
universe u
namespace CategoryTheory.Waldhausen.Fibration.AllWeak
variable {C : Type u} [SmallCategory C] (W : Structure C)

/-- The literal original relative evaluation is an equivalence for every W. -/
def relativeEvaluationHomotopyEquiv : ContinuousMap.HomotopyEquiv
    |SSet.diagonalSSet (RelativeRows.relativeSRows (nested W))|
      (waldhausenStructure W).Delooping :=
  RelativeRows.coarseEvaluationHomotopyEquiv (nested W) (extensionAxiom W)
    (jointData W) (jointData_secondEndpointSection W)

@[simp] theorem relativeEvaluationHomotopyEquiv_toFun :
    (relativeEvaluationHomotopyEquiv W).toFun =
      (SSet.toTop.map (RelativeRows.coarseEvaluation (nested W) (extensionAxiom W))).hom :=
  RelativeRows.coarseEvaluationHomotopyEquiv_toFun _ _ _ _

/-- The actual identity-relative total is contractible, without any fibration input. -/
instance relativeTotal_contractible :
    ContractibleSpace |SSet.diagonalSSet (RelativeRows.relativeSRows (nested W))| :=
  (relativeEvaluationHomotopyEquiv W).contractibleSpace

/-- The prescribed forward equivalence preserves the original zero point. -/
@[simp] theorem relativeCoarseEvaluation_hom_basepoint :
    TopCat.Hom.hom (Y := (waldhausenStructure W).Delooping)
      (SSet.toTop.map (RelativeRows.coarseEvaluation (nested W) (extensionAxiom W)))
      (RelativeRows.totalBasepoint (nested W)) = (waldhausenStructure W).kBasepoint := by
  exact RelativeRows.coarseEvaluation_basepoint (nested W) (extensionAxiom W)


end CategoryTheory.Waldhausen.Fibration.AllWeak
