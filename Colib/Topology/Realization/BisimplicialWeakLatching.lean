/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.BisimplicialLatchingEquivalences
public import Colib.Topology.Realization.MapWeakEquivalence
/-!
# Complete weak equivalences on actual bisimplicial latching objects

The original finite degeneracy-union pushouts and monomorphism HEP transfer
rowwise complete weakness to every partial and full outer latching object.
No coherent or pointwise continuous row inverse is assumed.

Implementation provenance:
`Quillen/Topology/Realization/BisimplicialWeakLatching.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open Topology TopCat SSet
open CategoryTheory Limits Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SSet.BisimplicialRealization
variable {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)

/-- Every partial latching comparison is a realization equivalence. The
induction uses genuine degeneracy-union pushouts and mono HEP. -/
theorem partialLatchingMap_isRealizationWeakEquivalence
    (h : ∀ n, IsRealizationWeakEquivalence (η.app (op ⦋n⦌))) :
    ∀ n k, k ≤ n + 1 → IsRealizationWeakEquivalence (partialLatchingMap η n k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ihn =>
    intro k
    induction k with
    | zero =>
      intro _
      exact IsRealizationWeakEquivalence.of_isInitial _
        (partialLatchingZeroIsInitial X n) (partialLatchingZeroIsInitial Y n)
    | succ k ihk =>
      intro hk
      have hk' : k < n + 1 := by omega
      have hlower : IsRealizationWeakEquivalence (lowerLatchingMap η n k) := by
        cases n with
        | zero =>
          exact IsRealizationWeakEquivalence.of_isInitial _
            SSet.Subcomplex.isInitialBot SSet.Subcomplex.isInitialBot
        | succ m => exact ihn m (by omega) k (by omega)
      exact IsRealizationWeakEquivalence.pushout
        (partialLatching_isPushout X n k hk').flip (partialLatching_isPushout Y n k hk').flip
        (lowerLatchingMap η n k) (η.app (op ⦋n⦌)) (partialLatchingMap η n k)
        (partialLatchingMap η n (k + 1))
        (lowerLatchingMap_ι η n k).symm (latchingFace_naturality η n k hk')
        (latchingCell_naturality η n k hk') (partialLatching_inclusion_naturality η n k)
        hlower (h n) (ihk (by omega))

/-- Full outer latching objects inherit every rowwise realization equivalence. -/
theorem latchingMap_isRealizationWeakEquivalence
    (h : ∀ n, IsRealizationWeakEquivalence (η.app (op ⦋n⦌))) (n : ℕ) :
    IsRealizationWeakEquivalence (latchingMap η n) := by
  cases n with
  | zero =>
    exact IsRealizationWeakEquivalence.of_isInitial _
      SSet.Subcomplex.isInitialBot SSet.Subcomplex.isInitialBot
  | succ n => exact partialLatchingMap_isRealizationWeakEquivalence η h n (n + 1) le_rfl

end SSet.BisimplicialRealization
