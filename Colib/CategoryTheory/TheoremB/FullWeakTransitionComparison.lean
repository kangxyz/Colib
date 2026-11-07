/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremB.WeakTransitionComparison
public import Colib.Topology.HomotopyFiber.ContractibleBase
public import Colib.Topology.HomotopyFiber.WeakBaseProjection

/-! # Complete weak-transition comma comparisons and contracted bases

Implementation source: `Quillen/CategoryTheory/TheoremB/FullWeakComparison.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The weak-transition result keeps
the original comma comparison and all components, including empty fibers.
-/
@[expose] public section

open CategoryTheory.TheoremA

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology CategoryTheory
universe u
namespace CategoryTheory.TheoremB
open TheoremA
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The original comma comparison is a complete weak equivalence at every target vertex,
including empty fibers and surjectivity on all path components. -/
theorem fiberComparison_isWeakHomotopyEquivalence_of_weakTransitions
    (h : TransitionWeakEquivalences F) (d : D) :
    IsWeakHomotopyEquivalence (fiberComparison F d) := by
  have hv := vertexFiberComparison_isWeakHomotopyEquivalence_of_weakCartesian (commaNerveDiagram F)
    (replacementPointAugmentation_transitionWeakCartesian (commaNerveDiagram F)
      (fun {_ _} f => h f)) d
  have hr : IsWeakHomotopyEquivalence (replacementStrictFiberComparison F d) := hv
  have hs := (isWeakHomotopyEquivalence_of_homotopyEquiv
    (replacementResolutionFiberEquiv F d)).comp hr
  rw [replacementResolutionFiberEquiv_comparison] at hs
  have ht := (isWeakHomotopyEquivalence_of_homotopyEquiv
    (resolutionFiberEquiv F d)).comp hs
  exact ht.of_homotopy (resolutionComparisonHomotopy F d)

/-- Over a specified contracted classifying-space base, the actual comma projection
itself is a weak equivalence; no replacement forward map is substituted. -/
theorem commaProjection_isWeakHomotopyEquivalence_of_contraction
    (h : TransitionWeakEquivalences F) (d : D)
    (H : (ContinuousMap.id (ClassifyingSpace D)).Homotopy
      (ContinuousMap.const (ClassifyingSpace D) (classifyingSpacePoint d))) :
    IsWeakHomotopyEquivalence (classifyingSpaceMap (CostructuredArrow.proj F d)).hom := by
  have hc := (isWeakHomotopyEquivalence_of_homotopyEquiv
    (HomotopyFiber.projectionEquivOfContraction (classifyingSpaceMap F).hom
      (classifyingSpacePoint d) H)).comp
        (fiberComparison_isWeakHomotopyEquivalence_of_weakTransitions F h d)
  rw [HomotopyFiber.projectionEquivOfContraction_toFun, fiberComparison_projection] at hc
  exact hc

/-- Weak contractibility of the actual base suffices for the original comma projection. -/
theorem commaProjection_isWeakHomotopyEquivalence_of_weakBase
    (h : TransitionWeakEquivalences F) (d : D)
    (hD : IsWeakHomotopyEquivalence (ContinuousMap.const (ClassifyingSpace D)
      (PUnit.unit : PUnit.{u + 1}))) :
    IsWeakHomotopyEquivalence (classifyingSpaceMap (CostructuredArrow.proj F d)).hom := by
  have hc := (HomotopyFiber.projection_isWeakHomotopyEquivalence_of_weakBase
    (classifyingSpaceMap F).hom (classifyingSpacePoint d) hD).comp
      (fiberComparison_isWeakHomotopyEquivalence_of_weakTransitions F h d)
  rw [fiberComparison_projection] at hc
  exact hc

end CategoryTheory.TheoremB
