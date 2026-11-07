/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.WeakCriterion
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceHomotopy
public import Colib.Topology.Homotopy.HomotopyGroup.Contractible

/-!
# Complete weak equivalences and the actual path-space fibers

Weakness of the actual fiber-to-point maps detects the original total map.
The existing native homotopy-invariance theorem is reused, rather than
redeclared through a parallel fiber proof. Nonemptiness and degree zero are retained.

Implementation provenance:
`Quillen/Topology/HomotopyFiber/WeakInvariance.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval
universe u v w
namespace Topology

/-- Weakness of every actual homotopy fiber's map to a point detects the
original total map, retaining nonemptiness and the zeroth homotopy set. -/
theorem isWeakHomotopyEquivalence_of_fiber_toPoint
    {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] (f : C(E, B))
    (h : ∀ b, IsWeakHomotopyEquivalence
      (ContinuousMap.const (HomotopyFiber f b) (PUnit.unit : PUnit.{u + 1}))) :
    IsWeakHomotopyEquivalence f := by
  apply HomotopyFiber.isWeakHomotopyEquivalence_of_fibers f
  · intro b
    obtain ⟨x, _⟩ := (h b).component_surjective PUnit.unit
    exact ⟨x⟩
  · intro b x n
    let : Subsingleton (HomotopyGroup.Pi n PUnit.{u + 1} PUnit.unit) :=
      subsingleton_pi_of_contractible n _ _
    exact ((h b).homotopy_bijective x n).injective.subsingleton

end Topology
