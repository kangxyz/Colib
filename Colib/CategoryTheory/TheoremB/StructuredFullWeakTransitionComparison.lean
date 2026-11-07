/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremB.FullWeakTransitionComparison

/-!
# The full weak equivalence for the original structured comparison

The opposite-comma identification and its explicit path homotopy transport the
all-component form of Theorem B to the original structured comparison. The map
in the conclusion is the reversed structure-arrow lift, at every target object.

Implementation source: `Quillen/CategoryTheory/TheoremB/StructuredFullWeakComparison.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open Topology CategoryTheory Opposite
universe u
namespace CategoryTheory.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The original structured comparison is a weak equivalence on all components
and at every basepoint whenever all its original transitions are weak equivalences. -/
theorem structuredFiberComparison_isWeakHomotopyEquivalence_of_weakTransitions
    (h : StructuredTransitionWeakEquivalences F) (d : D) :
    IsWeakHomotopyEquivalence (structuredFiberComparison F d) := by
  have hc := (fiberComparison_isWeakHomotopyEquivalence_of_weakTransitions F.op
    (transitionWeakEquivalences_op_of_structured F h) (op d)).comp
      (isWeakHomotopyEquivalence_of_homotopyEquiv (structuredCommaOppositeEquiv F d))
  have ht := (isWeakHomotopyEquivalence_of_homotopyEquiv
    (oppositeFiberHomeomorph F d).toHomotopyEquiv).comp hc
  exact ht.of_homotopy (structuredFiberComparisonTransportHomotopy F d)

end CategoryTheory.TheoremB
