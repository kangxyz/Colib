/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.WeakSquare
public import Colib.Topology.HomotopyFiber.Equivalence

/-!
# Finite all-point connectivity through actual homotopy squares

The explicit homotopy-fiber path-prefix equivalence transfers the finite bound under an original
homotopy. Applying the proved strict weak-square transfer twice then treats a homotopy-commuting
square with complete weak vertical maps. Every actual target and fiber point is retained.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyGroups/Connectivity/HomotopySquare.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

open scoped Topology unitInterval

universe u

namespace Topology.IsHomotopyConnectedMap

/-- An actual homotopy preserves finite connectivity of the original maps. -/
theorem of_homotopy {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} {n : ℕ} (hf : IsHomotopyConnectedMap f n) (H : f.Homotopy g) :
    IsHomotopyConnectedMap g n where
  fiber_nonempty y := ⟨(HomotopyFiber.homotopyEquiv H y).toFun
    (Classical.choice (hf.fiber_nonempty y))⟩
  fiber_subsingleton y z k hk := by
    let e := (HomotopyFiber.homotopyEquiv H y).symm
    let := hf.fiber_subsingleton y (e.toFun z) k hk
    exact (homotopyGroupMap_bijective_of_homotopyEquiv e
      (x := z) (y := e.toFun z) rfl k).injective.subsingleton

/-- Transfer the bound through the specified original homotopy square. No strict replacement
of that square is selected, and complete weak maps are required on both vertical sides. -/
theorem of_weak_homotopy_square {X Y A B : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A] [TopologicalSpace B]
    {p : C(X, A)} {q : C(Y, B)} (u : C(X, Y)) (v : C(A, B))
    (H : (v.comp p).Homotopy (q.comp u))
    (hu : IsWeakHomotopyEquivalence u) (hv : IsWeakHomotopyEquivalence v)
    (n : ℕ) (hq : IsHomotopyConnectedMap q n) : IsHomotopyConnectedMap p n := by
  have hqu : IsHomotopyConnectedMap (q.comp u) n :=
    of_weak_square u (ContinuousMap.id B) rfl hu (isWeakHomotopyEquivalence_id B) n hq
  have hvp : IsHomotopyConnectedMap (v.comp p) n := hqu.of_homotopy H.symm
  exact of_weak_square (ContinuousMap.id X) v rfl (isWeakHomotopyEquivalence_id X) hv n hvp

end Topology.IsHomotopyConnectedMap
