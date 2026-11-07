/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.GroupTheory.IsPerfect

/-! # Perfectness from a surjection whose kernel lies in the commutator

Extracted from `Quillen/Topology/HomotopyFiber/InjectiveH2Perfectness.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. This algebraic lemma supplies the
last step of the actual fiber exact-sequence argument; it assumes no homology
or homotopy-fiber recognition principle.
-/
@[expose] public section
universe u v
namespace Group

/-- A surjection to a perfect group with kernel in the commutator has perfect source. -/
theorem IsPerfect.of_surjective_of_ker_le_commutator
    {H : Type u} {G : Type v} [Group H] [Group G] [Group.IsPerfect G]
    (p : H →* G) (hp : Function.Surjective p) (hk : p.ker ≤ commutator H) :
    Group.IsPerfect H := by
  have hc : (commutator H).map p = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective p hp]
    exact Group.IsPerfect.commutator_eq_top
  refine ⟨top_unique ?_⟩
  intro a _
  have ha : p a ∈ (commutator H).map p := by rw [hc]; trivial
  obtain ⟨c, hc, he⟩ := ha
  have hk' : a * c⁻¹ ∈ commutator H := hk (by
    change p (a * c⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel])
  simpa only [inv_mul_cancel_right] using (commutator H).mul_mem hk' hc


end Group
