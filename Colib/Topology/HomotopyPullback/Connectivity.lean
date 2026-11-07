/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.Basic
public import Colib.Topology.HomotopyPullback.Fibration
public import Colib.Topology.HomotopyFiber.ContractibleBase

/-!
# Finite connectivity of the actual homotopy-pullback projection

The existing original fiber homotopy equivalence transfers each finite connectivity bound
without any separation condition. Over an explicitly contracted base, its actual fiber projection
also transfers the bound to finite homotopy sets of the total pullback. These are the bounded
fiber inputs for relative cube HELP, not a homotopy-excision assertion.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyPullback/Connectivity.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace Topology.HomotopyPullback

variable {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    (f : C(X, B)) (g : C(A, B)) {n : ℕ}

/-- The unchanged homotopy-pullback projection preserves the original finite connectivity bound. -/
theorem baseProjection_isHomotopyConnectedMap (hf : IsHomotopyConnectedMap f n) :
    IsHomotopyConnectedMap (baseProjection f g) n where
  fiber_nonempty a := (hf.fiber_nonempty (g a)).map (baseFiberHomotopyEquiv f g a)
  fiber_subsingleton a z k hk := by
    let e := (baseFiberHomotopyEquiv f g a).symm
    let := hf.fiber_subsingleton (g a) (e z) k hk
    exact (homotopyGroupMap_bijective_of_homotopyEquiv
      e (x := z) (y := e z) rfl k).injective.subsingleton

/-- Over the supplied contracted base, every total-space point has singleton homotopy sets
strictly below the original map's bound. The actual fiber projection is retained. -/
theorem subsingleton_homotopyGroup_of_contraction (hf : IsHomotopyConnectedMap f n)
    (a : A) (H : (ContinuousMap.id A).Homotopy (ContinuousMap.const A a))
    (z : HomotopyPullback f g) (k : ℕ) (hk : k < n) :
    Subsingleton (HomotopyGroup.Pi k (HomotopyPullback f g) z) := by
  let e := (HomotopyFiber.projectionEquivOfContraction (baseProjection f g) a H).symm
  let := (baseProjection_isHomotopyConnectedMap f g hf).fiber_subsingleton a (e z) k hk
  exact (homotopyGroupMap_bijective_of_homotopyEquiv
      e (x := z) (y := e z) rfl k).injective.subsingleton

end Topology.HomotopyPullback
