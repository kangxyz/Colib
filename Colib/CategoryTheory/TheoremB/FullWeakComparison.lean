/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.VertexFullComparison
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceHomotopy

/-!
# Quillen's Theorem B at every target object and on all components

The actual transition homotopy-equivalence hypothesis implies the complete
weak equivalence of the canonical comma comparison. Both component surjectivity
and all based homotopy-set bijections are included, even for empty fibers.

Implementation source: the first theorem in
`Quillen/CategoryTheory/TheoremB/FullWeakComparison.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd, specialized to the original transition
homotopy-equivalence hypothesis via strong finite-stage induction.
-/
@[expose] public noncomputable section
open Topology CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
namespace CategoryTheory.TheoremB
open TheoremA
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The original comma comparison is a complete weak equivalence at every target vertex,
including empty fibers and surjectivity on all path components. -/
theorem fiberComparison_isWeakHomotopyEquivalence
    (h : TransitionHomotopyEquivalences F) (d : D) :
    IsWeakHomotopyEquivalence (fiberComparison F d) := by
  have hv := vertexFiberComparison_isWeakHomotopyEquivalence (commaNerveDiagram F)
    (fun {_ _} f => ⟨transitionHomotopyEquiv F h f, rfl⟩) d
  have hr : IsWeakHomotopyEquivalence (replacementStrictFiberComparison F d) := hv
  have hs := (isWeakHomotopyEquivalence_of_homotopyEquiv
    (replacementResolutionFiberEquiv F d)).comp hr
  rw [replacementResolutionFiberEquiv_comparison] at hs
  have ht := (isWeakHomotopyEquivalence_of_homotopyEquiv
    (resolutionFiberEquiv F d)).comp hs
  exact ht.of_homotopy (resolutionComparisonHomotopy F d)

end CategoryTheory.TheoremB

attribute [colib_tag "COL-0248",
  colib_ref "WeibelKBook" "IV, 3.8, page 31" "adaptation"
    "The original transition homotopy-equivalence theorem, retaining actual comma-to-fiber maps"]
  CategoryTheory.TheoremB.fiberComparison_isWeakHomotopyEquivalence
