/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module


public import Colib.CategoryTheory.TheoremB.SkeletalWeakCartesianInduction
public import Colib.CategoryTheory.TheoremB.VertexWeakAssembly
public import Colib.Topology.HomotopyFiber.DiscreteWeakEquivalence
public import Colib.Topology.HomotopyFiber.WeakInvariance
public import Colib.Topology.HomotopyFiber.BasepointTransport
public import Colib.Topology.ClassifyingSpace.Connectivity

/-!
# Complete weak comparisons at replacement vertices

The skeletal weak-cartesian theorem and sequential assembly give complete
weakness of the original vertex-to-fiber comparison. Discrete-base restriction
retains component surjectivity. Weak diagram transitions suffice for the actual
point augmentation; no selected inverse homotopies are required.

Implementation provenance:
`Quillen/CategoryTheory/TheoremB/WeakVertexComparison.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. This supplies the weak-transition
case, retaining the original comparison; the existing native strong case
and discrete-fiber restriction are reused without redeclaration.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology Simplicial unitInterval
universe u v w
namespace Topology

/-- Actual pullbacks over singleton bases retain precisely their total source. -/
def pointBasePullbackHomeomorph {X A B : Type u}
    [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    [Unique A] [Subsingleton B] (q : C(X, B)) (g : C(A, B)) :
    HomotopyPullback q g ≃ₜ X where
  toFun z := z.val.2.1
  invFun x := ⟨(default, x, ContinuousMap.const unitInterval (g default)),
    Subsingleton.elim _ _, rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · apply Prod.ext
      · rfl
      · ext t
        exact Subsingleton.elim _ _
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Weakness of the actual horizontal map gives the original weak-cartesian
comparison when the two base spaces are singletons. -/
theorem weakCartesian_of_singleton_bases {W X A B : Type u}
    [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    [Unique A] [Subsingleton B]
    (p : C(W, A)) (q : C(X, B)) (f : C(W, X)) (g : C(A, B))
    (sq : q.comp f = g.comp p) (hf : IsWeakHomotopyEquivalence f) :
    Topology.HomotopyPullback.WeakCartesian p q f g sq := by
  have hc : IsWeakHomotopyEquivalence ((pointBasePullbackHomeomorph q g).toHomotopyEquiv.toFun.comp
      (HomotopyPullback.comparison q g p f sq)) := hf
  exact hc.of_comp_right
    (isWeakHomotopyEquivalence_of_homotopyEquiv (pointBasePullbackHomeomorph q g).toHomotopyEquiv)

/-- For a classifying-space target, weak contractibility of the original
fibers at object vertices suffices, using genuine path transport. -/
theorem isWeakHomotopyEquivalence_of_classifying_vertex_fibers
    {E : Type u} [TopologicalSpace E] {D : Type u} [SmallCategory D]
    (f : C(E, ClassifyingSpace D))
    (h : ∀ d : D, IsWeakHomotopyEquivalence
      (ContinuousMap.const (HomotopyFiber f (classifyingSpacePoint d))
        (PUnit.unit : PUnit.{u + 1}))) : IsWeakHomotopyEquivalence f := by
  apply isWeakHomotopyEquivalence_of_fiber_toPoint
  intro y
  obtain ⟨d, hd⟩ := classifyingSpace_joined_vertex y
  exact (h d).comp (isWeakHomotopyEquivalence_of_homotopyEquiv
    (HomotopyFiber.basepointTransportEquiv f hd.somePath).symm)

end Topology

namespace CategoryTheory.TheoremB
open Topology Topology.HomotopyPullback
open TheoremA CategoryTheory.TheoremB.Skeletal Topology.HomotopyPullback.Sequential
variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- Weak original diagram transitions give the actual point-augmentation
transition comparisons, without selected inverse homotopies. -/
theorem replacementPointAugmentation_transitionWeakCartesian
    (htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
      IsWeakHomotopyEquivalence (SSet.toTop.map (H.map f)).hom) :
    TransitionWeakCartesian (replacementPointAugmentation H) := by
  let : Unique |(Δ[0] : SSet.{u})| := uniqueOfSubsingleton (default : |(Δ[0] : SSet.{u})|)
  intro d e f
  let : Unique |((pointDiagram (D := D)).obj d)| :=
    { default := (default : |(Δ[0] : SSet.{u})|)
      uniq := fun x => Subsingleton.elim (α := |(Δ[0] : SSet.{u})|) x _ }
  let : Subsingleton |((pointDiagram (D := D)).obj e)| :=
    ⟨fun x y => Subsingleton.elim (α := |(Δ[0] : SSet.{u})|) x y⟩
  exact weakCartesian_of_singleton_bases _ _ _ _ _ (htrans f)

/-- The original vertex-to-fiber comparison is completely weak from genuine
weak transition squares, without finite-stage homotopy inverses. -/
theorem vertexFiberComparison_isWeakHomotopyEquivalence_of_weakCartesian
    (htrans : TransitionWeakCartesian (replacementPointAugmentation H)) (d : D) :
    IsWeakHomotopyEquivalence (vertexFiberComparison H d) := by
  have htotal := colimitComparison_isWeakHomotopyEquivalence_of_weakStages
    (replacementProjectionTowerMap H)
    (realizedReplacementSkeletonCocone H) (realizedReplacementSkeletonIsColimit H)
    replacementBaseSkeletonCocone replacementBaseSkeletonIsColimit
    (realizedReplacementSkeleton_closedEmbeddings H)
    (realizedReplacementSkeleton_closedEmbeddings pointDiagram) 1
    (fun n hn => stageComparison_isWeakHomotopyEquivalence
      (replacementPointAugmentation H) htrans 1 n hn)
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
