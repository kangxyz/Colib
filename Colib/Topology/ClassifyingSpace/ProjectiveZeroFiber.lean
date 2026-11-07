/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveZeroFiberEquivalence
public import Colib.Topology.ClassifyingSpace.UniverseHomotopy

/-!
# Realization of the original projective zero-fiber equivalence

This is the isomorphism fiber of the actual localized projection. Identifying
its structured comma category with a homotopy fiber still requires the
cartesian-lift and base-change hypotheses of Quillen's Theorem B.
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Topology SSet HomotopyGroup
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]

/-- The original group-completion realization is homotopy equivalent to the
actual zero isomorphism-fiber realization. -/
def completionZeroIsoFiberClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (GroupCompletionCategory R))
      (ClassifyingSpace (ZeroIsoFiber R)) :=
  equivalenceClassifyingHomotopyEquivUniversal (completionZeroIsoFiberEquivalence R)

@[simp]
lemma completionZeroIsoFiberClassifyingHomotopyEquiv_toFun :
    (completionZeroIsoFiberClassifyingHomotopyEquiv R).toFun =
      classifyingSpaceMapUniversal (completionZeroIsoFiberEntry R) :=
  equivalenceClassifyingHomotopyEquivUniversal_toFun _

end ModuleCat.FiniteProjective
