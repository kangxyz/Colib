/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.WeakSquare
public import Colib.Topology.HomotopyFiber.SquareEquivalence
public import Colib.Topology.HomotopyFiber.BasepointTransport

/-!
# Finite connectivity through original homotopy-equivalence squares

A strictly commuting square of genuine homotopy equivalences preserves the finite connectivity
of the unchanged arrow in both directions. The forward direction transports every target fiber
along the actual inverse homotopy; it does not replace point coverage by a chosen-basepoint test.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyGroups/Connectivity/EquivalenceSquare.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section
noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace Topology.IsHomotopyConnectedMap
variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B] {p : C(X, A)} {q : C(Y, B)}

/-- Finite connectivity transfers forward, including all components and arbitrary fiber points. -/
theorem of_equivalence_square
    (e : ContinuousMap.HomotopyEquiv X Y) (eb : ContinuousMap.HomotopyEquiv A B)
    (sq : eb.toFun.comp p = q.comp e.toFun) (n : ℕ)
    (hp : IsHomotopyConnectedMap p n) : IsHomotopyConnectedMap q n := by
  have he (b : B) : Nonempty (ContinuousMap.HomotopyEquiv
      (HomotopyFiber p (eb.invFun b)) (HomotopyFiber q b)) := by
    let γ : Path (eb (eb.invFun b)) b := eb.right_inv.some.evalAt b
    exact ⟨(HomotopyFiber.mapHomotopyEquivOfEquivalences e eb sq (eb.invFun b)).trans
      (HomotopyFiber.basepointTransportEquiv q γ)⟩
  constructor
  · intro b
    exact (hp.fiber_nonempty (eb.invFun b)).map (he b).some
  · intro b z k hk
    let ef := (he b).some.symm
    let := hp.fiber_subsingleton (eb.invFun b) (ef z) k hk
    exact (homotopyGroupMap_bijective_of_homotopyEquiv
      ef (x := z) (y := ef z) rfl k).injective.subsingleton

/-- The original strict equivalence square preserves exactly the same finite connectivity range. -/
theorem iff_of_equivalence_square
    (e : ContinuousMap.HomotopyEquiv X Y) (eb : ContinuousMap.HomotopyEquiv A B)
    (sq : eb.toFun.comp p = q.comp e.toFun) (n : ℕ) :
    IsHomotopyConnectedMap p n ↔ IsHomotopyConnectedMap q n :=
  ⟨of_equivalence_square e eb sq n,
    of_weak_square e.toFun eb.toFun sq
      (isWeakHomotopyEquivalence_of_homotopyEquiv e)
      (isWeakHomotopyEquivalence_of_homotopyEquiv eb) n⟩

end Topology.IsHomotopyConnectedMap
