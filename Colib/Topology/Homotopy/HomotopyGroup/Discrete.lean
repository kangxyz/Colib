/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Map
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Actual positive homotopy groups of discrete spaces

Continuous positive-dimensional cubes are literally constant; the original
based homotopy quotient therefore has one element in every positive degree.

Implementation provenance: `Quillen/Topology/HomotopyGroups/Discrete.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps and universes are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology
universe u v
namespace Topology

/-- Positive-dimensional cubes in a discrete space are the actual constant loops. -/
theorem _root_.GenLoop.eq_const_of_discrete {X : Type u} [TopologicalSpace X]
    [DiscreteTopology X] (x : X) (n : ℕ) (p : GenLoop (Fin (n + 1)) X x) :
    p = GenLoop.const := by
  apply GenLoop.ext
  intro z
  exact (PreconnectedSpace.constant inferInstance p.val.continuous
    (x := z) (y := fun _ ↦ 0)).trans (p.property _ ⟨0, Or.inl rfl⟩)

/-- Discrete spaces have trivial original homotopy groups in every positive degree. -/
theorem _root_.HomotopyGroup.subsingleton_positive_of_discrete {X : Type u} [TopologicalSpace X]
    [DiscreteTopology X] (x : X) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi (n + 1) X x) := by
  refine ⟨?_⟩
  intro a b
  induction a using Quotient.inductionOn with | _ a =>
    induction b using Quotient.inductionOn with | _ b =>
      rw [_root_.GenLoop.eq_const_of_discrete x n a, _root_.GenLoop.eq_const_of_discrete x n b]

end Topology
