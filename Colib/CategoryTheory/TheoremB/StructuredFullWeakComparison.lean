/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.FullWeakComparison
public import Colib.CategoryTheory.TheoremB.StructuredTransport

/-!
# Complete structured-arrow Theorem B

Opposite-comma equivalence and the actual parameter homotopy preserve the
canonical structured comparison at every target object and on all components.
Its paths run from the image of the source to the target object.

Implementation source: `Quillen/CategoryTheory/TheoremB/StructuredFullWeakComparison.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd, specialized to the original transition
homotopy-equivalence hypothesis rather than weak-transition induction.
-/
@[expose] public noncomputable section
open Topology CategoryTheory Opposite
universe u
namespace CategoryTheory.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The original structured comparison is a weak equivalence on all components
and at every basepoint under its original transition homotopy-equivalence hypothesis. -/
theorem structuredFiberComparison_isWeakHomotopyEquivalence
    (h : StructuredTransitionHomotopyEquivalences F) (d : D) :
    IsWeakHomotopyEquivalence (structuredFiberComparison F d) := by
  have hc := (fiberComparison_isWeakHomotopyEquivalence F.op
    (transitionHomotopyEquivalences_op_of_structured F h) (op d)).comp
      (isWeakHomotopyEquivalence_of_homotopyEquiv (structuredCommaOppositeEquiv F d))
  have ht := (isWeakHomotopyEquivalence_of_homotopyEquiv
    (oppositeFiberHomeomorph F d).toHomotopyEquiv).comp hc
  exact ht.of_homotopy (structuredFiberComparisonTransportHomotopy F d)

end CategoryTheory.TheoremB

attribute [colib_tag "COL-0248",
  colib_ref "WeibelKBook" "IV, 3.8, page 31" "adaptation"
    "The original transition homotopy-equivalence theorem, retaining actual comma-to-fiber maps"]
  CategoryTheory.TheoremB.structuredFiberComparison_isWeakHomotopyEquivalence
