/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.Basic
public import Colib.Topology.HomotopyFiber.WeakSquareTransport

/-!
# Finite connectivity transported through the original weak square

The unchanged original homotopy-fiber map of a strict square with weak total and base maps
is a complete weak equivalence. Its component coverage transfers actual fiber nonemptiness,
and its homotopy-set injections transfer the finite bound at every original fiber point.
No chosen inverse map, connectedness assumption, or higher-dimensional bound is introduced.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyGroups/Connectivity/WeakSquare.lean` at commit
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

/-- Transfer a finite bound through the actual strictly commuting weak square, retaining
nonempty fibers and all their basepoints, including the zeroth connectivity bound. -/
theorem of_weak_square (u : C(X, Y)) (v : C(A, B)) (sq : v.comp p = q.comp u)
    (hu : IsWeakHomotopyEquivalence u) (hv : IsWeakHomotopyEquivalence v)
    (n : ℕ) (hq : IsHomotopyConnectedMap q n) : IsHomotopyConnectedMap p n where
  fiber_nonempty a := by
    let z := Classical.choice (hq.fiber_nonempty (v a))
    obtain ⟨w, _⟩ :=
      (HomotopyFiber.map_isWeakHomotopyEquivalence u v sq hu hv a).component_surjective z
    exact ⟨w⟩
  fiber_subsingleton a z k hk := by
    let := hq.fiber_subsingleton (v a) (HomotopyFiber.map u v sq a z) k hk
    have h := (HomotopyFiber.map_isWeakHomotopyEquivalence u v sq hu hv a).homotopy_bijective z k
    exact h.injective.subsingleton

end Topology.IsHomotopyConnectedMap
