/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.WeakCoproduct

/-! # Original weak-cartesian comparisons assemble over coproduct parameters

The canonical fixed-target comparison factors literally through the original
sigma map of the summand comparisons and the actual pullback/coproduct
homeomorphism. Weak coproduct closure and that homeomorphism prove the result.
No finite pushout or global realization fiber theorem is assumed.


Implementation provenance:
`Quillen/Topology/HomotopyPullback/WeakCoproduct.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u
namespace Topology.HomotopyPullback
open Topology.HomotopyPullback
variable {ι : Type u} {X A : ι → Type u} [∀ i, TopologicalSpace (X i)]
  [∀ i, TopologicalSpace (A i)]
  {E T : Type u} [TopologicalSpace E] [TopologicalSpace T]
  (q : C(E, T)) (s : ∀ i, C(A i, T)) (p : ∀ i, C(X i, A i)) (t : ∀ i, C(X i, E))
  (w : ∀ i, q.comp (t i) = (s i).comp (p i))

/-- The original constant-path comparison is literally the sigma comparison
followed by the actual pullback/coproduct coordinate homeomorphism. -/
theorem comparison_sigma_factorization :
    comparison q (ContinuousMap.sigma s) (sigmaMap p) (ContinuousMap.sigma t)
      (sigmaFixedSquare q s p t w) =
      (sigmaPullbackMap q s).comp (sigmaMap (fun i ↦ comparison q (s i) (p i) (t i) (w i))) := rfl

/-- Weak cartesianness of the original component squares gives weak
cartesianness of their original coproduct square, including empty components. -/
theorem comparison_sigma_isWeakHomotopyEquivalence
    (h : ∀ i, IsWeakHomotopyEquivalence (comparison q (s i) (p i) (t i) (w i))) :
    IsWeakHomotopyEquivalence (comparison q (ContinuousMap.sigma s) (sigmaMap p)
      (ContinuousMap.sigma t) (sigmaFixedSquare q s p t w)) := by
  rw [comparison_sigma_factorization q s p t w]
  exact (isWeakHomotopyEquivalence_of_homotopyEquiv
    (sigmaPullbackHomeomorph q s).toHomotopyEquiv).comp
      (WeakCoproduct.isWeakHomotopyEquivalence_sigma
        (fun i ↦ comparison q (s i) (p i) (t i) (w i)) h)

end Topology.HomotopyPullback
