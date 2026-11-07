/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.Cube.ThinSupport
public import Mathlib.Data.Fintype.Fin

/-!
# The actual vertical-column count for thin supports

The first coordinate is the path coordinate; the remaining d coordinates are the parameters.
A point with p+1 coordinates in a band forces at least p parameter coordinates into that band.
Consequently, for d < p+q, a fixed vertical column cannot meet the two thin supports in
disjoint bands, even at different path times. The map consumer retains the original family.
No connectivity or point-set hypothesis is needed for this finite combinatorial step.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/Cube/ThinSupportColumns.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology

open scoped Topology unitInterval

universe u

namespace Cube

variable {d : ℕ}

/-- Separating the actual path coordinate gives the exact coordinate count. -/
theorem bandCoordinates_cons_card (a b t : unitInterval) (x : Fin d → unitInterval) :
    (bandCoordinates a b (Fin.cons t x)).card =
      (bandCoordinates a b x).card + if a < t ∧ t < b then 1 else 0 := by
  classical
  simp only [bandCoordinates, Fin.card_filter_univ_succ', Fin.cons_zero, Fin.cons_succ]
  exact Nat.add_comm _ _

/-- The path coordinate can account for at most one of the required band coordinates. -/
theorem thinSupport_cons_imp (a b t : unitInterval) (p : ℕ) (x : Fin d → unitInterval)
    (hx : Fin.cons t x ∈ thinSupport a b (p + 1)) : x ∈ thinSupport a b p := by
  change p + 1 ≤ (bandCoordinates a b (Fin.cons t x)).card at hx
  rw [bandCoordinates_cons_card] at hx
  change p ≤ (bandCoordinates a b x).card
  split_ifs at hx <;> omega

/-- Different original path times on one vertical column still cannot hit both supports. -/
theorem column_not_mem_both (a b c e : unitInterval) (hbc : b ≤ c)
    (p q : ℕ) (hd : d < p + q) (x : Fin d → unitInterval) (s t : unitInterval)
    (hx : Fin.cons s x ∈ thinSupport a b (p + 1)) :
    Fin.cons t x ∉ thinSupport c e (q + 1) := by
  intro hy
  exact Set.disjoint_left.mp (thinSupport_disjoint a b c e hbc p q hd)
    (thinSupport_cons_imp a b s p x hx) (thinSupport_cons_imp c e t q x hy)

/-- Every actual vertical column avoids one of the entire two supports. This also covers
p = 0 or q = 0 whenever the displayed dimension inequality is possible. -/
theorem column_avoids_one (a b c e : unitInterval) (hbc : b ≤ c)
    (p q : ℕ) (hd : d < p + q) (x : Fin d → unitInterval) :
    (∀ t, Fin.cons t x ∉ thinSupport a b (p + 1)) ∨
      ∀ t, Fin.cons t x ∉ thinSupport c e (q + 1) := by
  classical
  by_cases h : ∃ s, Fin.cons s x ∈ thinSupport a b (p + 1)
  · obtain ⟨s, hs⟩ := h
    exact Or.inr (fun t ↦ column_not_mem_both a b c e hbc p q hd x s t hs)
  · exact Or.inl (fun t ht ↦ h ⟨t, ht⟩)

/-- Original families with the two established support bounds have every vertical path
contained in one of the two original covering subsets. No path is replaced or reparameterized. -/
theorem column_image_subset_one (a b c e : unitInterval) (hbc : b ≤ c)
    (p q : ℕ) (hd : d < p + q) {Y : Type u} [TopologicalSpace Y]
    (F : C((Fin (d + 1) → unitInterval), Y)) (U V : Set Y)
    (hcover : ∀ z, F z ∈ U ∪ V)
    (hU : F ⁻¹' (U \ V) ⊆ thinSupport a b (p + 1))
    (hV : F ⁻¹' (V \ U) ⊆ thinSupport c e (q + 1))
    (x : Fin d → unitInterval) :
    (∀ t, F (Fin.cons t x) ∈ U) ∨ ∀ t, F (Fin.cons t x) ∈ V := by
  rcases column_avoids_one a b c e hbc p q hd x with h | h
  · right
    intro t
    rcases hcover (Fin.cons t x) with ht | ht
    · by_contra hn
      exact h t (hU ⟨ht, hn⟩)
    · exact ht
  · left
    intro t
    rcases hcover (Fin.cons t x) with ht | ht
    · exact ht
    · by_contra hn
      exact h t (hV ⟨ht, hn⟩)

end Cube
