/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.SkeletalCartesianInduction
public import Colib.CategoryTheory.TheoremB.VertexWeakAssembly
public import Colib.Topology.HomotopyFiber.DiscreteWeakEquivalence

/-!
# Complete weak comparison at every replacement vertex

Actual transition homotopy equivalences imply the finite cartesian stages.
Compact assembly supplies both all-degree based bijectivity and surjectivity
on all path components, including when a diagram value is empty.

Implementation source: the complete vertex comparison in
`Quillen/CategoryTheory/TheoremB/WeakVertexComparison.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd, using the original strong transition
hypothesis and proved homotopy-equivalence stage comparisons.
-/
@[expose] public noncomputable section
open Topology CategoryTheory Limits
open scoped Topology Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB
open TheoremA Skeletal Topology.HomotopyPullback.Sequential
variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The original vertex comparison is a complete weak equivalence from actual
transition homotopy equivalences, including empty values and every component. -/
theorem vertexFiberComparison_isWeakHomotopyEquivalence
    (htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
      ∃ E : ContinuousMap.HomotopyEquiv |H.obj d| |H.obj e|,
        E.toFun = (SSet.toTop.map (H.map f)).hom) (d : D) :
    IsWeakHomotopyEquivalence (vertexFiberComparison H d) := by
  have htotal : IsWeakHomotopyEquivalence (vertexPullbackComparison H) := {
    component_surjective := colimitComparison_component_surjective
      (replacementProjectionTowerMap H)
      (realizedReplacementSkeletonCocone H) (realizedReplacementSkeletonIsColimit H)
      replacementBaseSkeletonCocone replacementBaseSkeletonIsColimit
      (realizedReplacementSkeleton_closedEmbeddings H)
      (realizedReplacementSkeleton_closedEmbeddings pointDiagram) 1
      (fun n hn => stageComparisonHomotopyEquiv H htrans 1 n hn)
      (fun n hn => stageComparisonHomotopyEquiv_toFun H htrans 1 n hn)
    homotopy_bijective := colimitComparison_homotopyGroupMap_bijective
      (replacementProjectionTowerMap H)
      (realizedReplacementSkeletonCocone H) (realizedReplacementSkeletonIsColimit H)
      replacementBaseSkeletonCocone replacementBaseSkeletonIsColimit
      (realizedReplacementSkeleton_closedEmbeddings H)
      (realizedReplacementSkeleton_closedEmbeddings pointDiagram) 1
      (fun n hn => stageComparisonHomotopyEquiv H htrans 1 n hn)
      (fun n hn => stageComparisonHomotopyEquiv_toFun H htrans 1 n hn) }
  have hf := discreteStrictFiberMap_isWeakHomotopyEquivalence
    (replacementStageOneProjection H) (vertexPullbackProjection H)
    (vertexPullbackComparison H) rfl (pointStageOneVertex d) htotal
  have hc := (isWeakHomotopyEquivalence_of_homotopyEquiv
    (vertexPullbackFiberHomeomorph H d).toHomotopyEquiv).comp
      (hf.comp (isWeakHomotopyEquivalence_of_homotopyEquiv
        (stageOneFiberHomeomorph H d).toHomotopyEquiv))
  change IsWeakHomotopyEquivalence ((vertexPullbackFiberHomeomorph H d).toHomotopyEquiv.toFun.comp
    ((vertexRestrictedComparison H d).comp
      (stageOneFiberHomeomorph H d).toHomotopyEquiv.toFun)) at hc
  have he : (vertexPullbackFiberHomeomorph H d).toHomotopyEquiv.toFun.comp
      ((vertexRestrictedComparison H d).comp
        (stageOneFiberHomeomorph H d).toHomotopyEquiv.toFun) = vertexFiberComparison H d :=
    vertexPullbackFiberHomeomorph_comparison H d
  exact (congrArg IsWeakHomotopyEquivalence he).mp hc

end CategoryTheory.TheoremB
