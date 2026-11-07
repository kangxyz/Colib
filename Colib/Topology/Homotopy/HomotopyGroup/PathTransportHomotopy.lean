/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportNaturality

/-!
# Homotopy invariance and reversal of the original basepoint transport

The original free-path-evaluation transport depends only on the endpoint-fixed
homotopy class of its path. Reversing the path gives its inverse. Both statements
hold in every finite degree, including degree zero, and follow from actual
continuous squares.
-/

/-! Implementation source: `Quillen/Topology/HomotopyGroups/PathTransportHomotopy.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, endpoint paths,
universes and signs are retained, with native Colib dependencies. -/
@[expose] public section

noncomputable section

open scoped Topology unitInterval

universe u

namespace Topology

variable {X : Type u} [TopologicalSpace X] {x y : X}

/-- Endpoint-fixed homotopic paths induce equal original transports in every degree. -/
theorem pathTransport_eq_of_homotopic {p q : Path x y} (h : p.Homotopic q) (n : ℕ) :
    pathTransport p n = pathTransport q n := by
  obtain ⟨H⟩ := h
  apply Equiv.ext
  intro a
  have hs := pathTransport_square p q (Path.refl x) (Path.refl y) H.toContinuousMap
    H.map_zero_left H.map_one_left
    (fun t ↦ H.source t) (fun t ↦ H.target t) n a
  simpa only [pathTransport_refl, Equiv.refl_apply] using hs.symm

/-- Reversing a path undoes its original all-degree basepoint transport. -/
@[simp]
theorem pathTransport_symm_apply (p : Path x y) (n : ℕ)
    (a : HomotopyGroup.Pi n X x) :
    pathTransport p.symm n (pathTransport p n a) = a := by
  let H : C(unitInterval × unitInterval, X) :=
    ⟨fun z ↦ p (Set.Icc.convexComb z.1 0 z.2), by fun_prop⟩
  have hs := pathTransport_square (Path.refl x) p.symm p (Path.refl x) H
    (by intro t; simp [H]) (by
      intro t
      change p (Set.Icc.convexComb 1 0 t) = p (unitInterval.symm t)
      congr 1
      apply Subtype.ext
      simp [Set.Icc.convexComb, unitInterval.symm])
    (by intro t; simp [H]) (by intro t; simp [H]) n a
  simpa only [pathTransport_refl, Equiv.refl_apply] using hs

end Topology
