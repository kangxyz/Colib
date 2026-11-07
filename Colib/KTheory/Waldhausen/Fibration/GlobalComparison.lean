/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Fibration.AllWeak.TotalFiberSquare
public import Colib.KTheory.Waldhausen.Fibration.AllWeak.RelativeContractible
public import Colib.KTheory.Waldhausen.Fibration.AllWeak.CanonicalFiberFactorization
public import Colib.Topology.HomotopyFiber.CommonBaseSquareTransport
public import Colib.Topology.HomotopyFiber.BasedSquareMap
public import Colib.KTheory.Waldhausen.Fibration.RelativeRows.WeakTotalFiber

/-! # The original global change-of-weak-equivalences fiber comparison

The proved original total-tail comparisons, their common-base square, and
the actual coarse evaluation identify the original canonical acyclic map
with a weak equivalence onto the homotopy fiber of `changeWeakMap`.
The category is small; extension, two-out-of-three, joint cylinder data and
its genuine second-endpoint section are explicit structural hypotheses.


Implementation provenance:
`Quillen/Waldhausen/Fibration/GlobalComparison.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.Fibration.RelativeRows


noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


namespace CategoryTheory.Waldhausen.Fibration.AllWeak
open RelativeRows
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The original all-weak tail after its actual base homeomorphism. -/
def commonBaseAllWeakTail : C(
    |SSet.diagonalSSet (relativeSRows (nested (acyclicStructure N)))|,
    |SSet.diagonalSSet (ordinarySRows (acyclicStructure N))|) :=
  (ordinaryTotalInclusionMap (acyclicStructure N)).comp
    (totalTailMap (nested (acyclicStructure N)))

/-- The actual constant comparison, merely expressed over the common base. -/
def commonBaseAllWeakComparison : C((acyclicStructure N).Delooping,
    HomotopyFiber (commonBaseAllWeakTail N) (ordinaryTotalBasepoint (acyclicStructure N))) where
  toFun x := HomotopyFiber.basepoint (commonBaseAllWeakTail N)
    (ordinaryTotalBasepoint (acyclicStructure N))
    (SSet.toTop.map (totalFiberInclusion (nested (acyclicStructure N))) x) (by
      change ordinaryTotalInclusionMap (acyclicStructure N)
        (totalTailMap (nested (acyclicStructure N)) _) = _
      rw [totalTailMap_totalFiberInclusion, ordinaryTotalInclusionMap_basepoint])
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (SSet.toTop.map (totalFiberInclusion (nested (acyclicStructure N)))).hom.continuous.prodMk
      continuous_const

/-- The original homeomorphism, without stronger total-tail hypotheses. -/
theorem commonBaseAllWeakComparison_weak
    (h : IsWeakHomotopyEquivalence (totalTailFiberComparison (nested (acyclicStructure N)))) :
    IsWeakHomotopyEquivalence (commonBaseAllWeakComparison N) := by
  have hm := HomotopyFiber.mapAt_weak
    (p := totalTailMap (nested (acyclicStructure N))) (q := commonBaseAllWeakTail N)
    (ContinuousMap.id _) (ordinaryTotalInclusionMap (acyclicStructure N)) rfl
    (isWeakHomotopyEquivalence_id _)
    (isWeakHomotopyEquivalence_of_homotopyEquiv (ordinaryTotalHomeomorph (acyclicStructure
      N)).toHomotopyEquiv)
    (ordinaryTotalBasepoint (acyclicStructure (nested (acyclicStructure N))))
    (ordinaryTotalBasepoint (acyclicStructure N))
    (ordinaryTotalInclusionMap_basepoint (acyclicStructure N))
  have hh := hm.comp h
  convert hh using 1
  ext x
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · ext t
    exact (ordinaryTotalInclusionMap_basepoint (acyclicStructure N)).symm

/-- The original split-fiber square, now on actual realizations. -/
theorem totalFiberInclusion_relativeInclusion_realized :
    (SSet.toTop.map (totalFiberInclusion N)).hom.comp (acyclicInclusionMap N) =
      (relativeTotalInclusionMap N).comp
        (SSet.toTop.map (totalFiberInclusion (nested (acyclicStructure N)))).hom := by
  have h := congrArg (fun f ↦ (SSet.toTop.map f).hom) (totalFiberInclusion_relativeInclusion N)
  simpa only [Functor.map_comp, TopCat.hom_comp, relativeTotalInclusionMap,
    acyclicInclusionMap, deloopingMap] using h.symm

/-- Common-base transport makes the original relative split square cartesian. -/
theorem relativeSplitComparison_weak
    (hN : IsWeakHomotopyEquivalence (totalTailFiberComparison N))
    (hA : IsWeakHomotopyEquivalence (totalTailFiberComparison (nested (acyclicStructure N)))) :
    IsWeakHomotopyEquivalence (HomotopyPullback.comparison
      (SSet.toTop.map (totalFiberInclusion N)).hom (relativeTotalInclusionMap N)
      (SSet.toTop.map (totalFiberInclusion (nested (acyclicStructure N)))).hom
      (acyclicInclusionMap N) (totalFiberInclusion_relativeInclusion_realized N)) := by
  apply HomotopyFiber.fiberModelComparison_isWeakHomotopyEquivalence
    (commonBaseAllWeakTail N) (totalTailMap N) (relativeTotalInclusionMap N)
    (relativeTotalInclusion_tail N).symm (ordinaryTotalBasepoint (acyclicStructure N))
    (SSet.toTop.map (totalFiberInclusion (nested (acyclicStructure N)))).hom
    (SSet.toTop.map (totalFiberInclusion N)).hom (acyclicInclusionMap N)
    (totalFiberInclusion_relativeInclusion_realized N)
    (commonBaseAllWeakComparison N) (totalTailFiberComparison N) rfl rfl
  · ext x
    apply Subtype.ext
    apply Prod.ext
    · exact (ContinuousMap.congr_fun (totalFiberInclusion_relativeInclusion_realized N) x).symm
    · rfl
  · exact commonBaseAllWeakComparison_weak N hA
  · exact hN

/-- Original split-fiber map between the actual relative-inclusion fibers. -/
def relativeSplitFiberMap : C(
    HomotopyFiber (SSet.toTop.map (totalFiberInclusion (nested (acyclicStructure N)))).hom
      (totalBasepoint (nested (acyclicStructure N))),
    HomotopyFiber (SSet.toTop.map (totalFiberInclusion N)).hom (totalBasepoint N)) :=
  HomotopyFiber.mapAt (acyclicInclusionMap N) (relativeTotalInclusionMap N)
    (totalFiberInclusion_relativeInclusion_realized N).symm
    (totalBasepoint (nested (acyclicStructure N))) (totalBasepoint N)
    (relativeInclusionTotal_basepoint N)

/-- Exact original split cartesianness gives the exact map of its fibers. -/
theorem relativeSplitFiberMap_weak
    (hN : IsWeakHomotopyEquivalence (totalTailFiberComparison N))
    (hA : IsWeakHomotopyEquivalence (totalTailFiberComparison (nested (acyclicStructure N)))) :
    IsWeakHomotopyEquivalence (relativeSplitFiberMap N) :=
  HomotopyFiber.mapAt_weak_of_comparison (acyclicInclusionMap N) (relativeTotalInclusionMap N)
    (totalFiberInclusion_relativeInclusion_realized N).symm (relativeSplitComparison_weak N hN hA)
    (totalBasepoint (nested (acyclicStructure N))) (totalBasepoint N)
    (relativeInclusionTotal_basepoint N)

/-- Evaluation retains the original fine source point and evaluates its complete path. -/
def evaluationFiberMap (he : ExtensionAxiom N.coarse) : C(
    HomotopyFiber (SSet.toTop.map (totalFiberInclusion N)).hom (totalBasepoint N),
    HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint) :=
  HomotopyFiber.mapAt (ContinuousMap.id _) (SSet.toTop.map (coarseEvaluation N he)).hom
    (totalFiberInclusion_coarseEvaluation_realized N he)
    (totalBasepoint N) N.coarse.kBasepoint (coarseEvaluation_basepoint N he)

/-- The genuine original coarse evaluation supplies the needed weak fiber map. -/
theorem evaluationFiberMap_weak (he : ExtensionAxiom N.coarse)
    [N.coarse.weq.HasTwoOutOfThreeProperty] (D : RowFactorization.JointData N)
    (hs : RowFactorization.SecondEndpointSection N D) :
    IsWeakHomotopyEquivalence (evaluationFiberMap N he) := by
  apply HomotopyFiber.mapAt_weak (ContinuousMap.id _)
    (SSet.toTop.map (coarseEvaluation N he)).hom
    (totalFiberInclusion_coarseEvaluation_realized N he)
    (isWeakHomotopyEquivalence_id _)
  have h := isWeakHomotopyEquivalence_of_homotopyEquiv (coarseEvaluationHomotopyEquiv N he D hs)
  rwa [coarseEvaluationHomotopyEquiv_toFun] at h

variable [N.coarse.weq.HasTwoOutOfThreeProperty]

/-- The original evaluated square retains its complete postcomposed path. -/
theorem evaluationFiberMap_relativeSplitFiberMap (he : ExtensionAxiom N.coarse) :
    (evaluationFiberMap N he).comp (relativeSplitFiberMap N) =
      (acyclicFiberSquareMap N).comp
        (evaluationFiberMap (nested (acyclicStructure N)) (extensionAxiom (acyclicStructure N)))
          := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    have h := congrArg (fun f ↦ (SSet.toTop.map f).hom)
      (relativeInclusionTotal_coarseEvaluation N he)
    rw [Functor.map_comp, Functor.map_comp, TopCat.hom_comp, TopCat.hom_comp] at h
    exact ContinuousMap.congr_fun h (z.1.2 t)

/-- The two original total comparisons suffice for the original
acyclic-square fiber comparison; the evaluation hypotheses are structural. -/
theorem acyclicFiberSquareMap_weak_of_totalComparisons
    (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N)
    (hs : RowFactorization.SecondEndpointSection N D)
    (hN : IsWeakHomotopyEquivalence (totalTailFiberComparison N))
    (hA : IsWeakHomotopyEquivalence (totalTailFiberComparison (nested (acyclicStructure N)))) :
    IsWeakHomotopyEquivalence (acyclicFiberSquareMap N) := by
  have h := (evaluationFiberMap_weak N he D hs).comp (relativeSplitFiberMap_weak N hN hA)
  rw [evaluationFiberMap_relativeSplitFiberMap N he] at h
  exact h.of_comp_left (evaluationFiberMap_weak (nested (acyclicStructure N))
    (extensionAxiom (acyclicStructure N)) (jointData (acyclicStructure N))
    (jointData_secondEndpointSection (acyclicStructure N)))

/-- Assembly of the exact original canonical comparison from given total-tail
weak equivalences. The final theorem below supplies both from the original model. -/
theorem canonicalFiberMap_weak_of_totalComparisons
    (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N)
    (hs : RowFactorization.SecondEndpointSection N D)
    (hN : IsWeakHomotopyEquivalence (totalTailFiberComparison N))
    (hA : IsWeakHomotopyEquivalence (totalTailFiberComparison (nested (acyclicStructure N)))) :
    IsWeakHomotopyEquivalence (canonicalFiberMap N) := by
  have h := (acyclicFiberSquareMap_weak_of_totalComparisons N he D hs hN hA).comp
    (isWeakHomotopyEquivalence_of_homotopyEquiv (changeWeakFiberLiftEquiv (acyclicStructure N)))
  change IsWeakHomotopyEquivalence
    ((acyclicFiberSquareMap N).comp (changeWeakFiberLift (acyclicStructure N))) at h
  rwa [acyclicFiberSquareMap_changeWeakFiberLift] at h
end CategoryTheory.Waldhausen.Fibration.AllWeak

namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V) [N.coarse.weq.HasTwoOutOfThreeProperty]

/-- Global change of weak equivalences with the original canonical fiber map. -/
theorem canonicalFiberMap_isWeakHomotopyEquivalence
    (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N)
    (hs : RowFactorization.SecondEndpointSection N D) :
    IsWeakHomotopyEquivalence (canonicalFiberMap N) :=
  AllWeak.canonicalFiberMap_weak_of_totalComparisons N he D hs
    (RelativeRows.totalTailFiberComparison_isWeakHomotopyEquivalence N)
    (RelativeRows.totalTailFiberComparison_isWeakHomotopyEquivalence
      (AllWeak.nested (acyclicStructure N)))
end CategoryTheory.Waldhausen.Fibration
