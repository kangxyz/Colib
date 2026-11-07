/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.Analysis.Convex.StdSimplex.Boundary
public import Mathlib.Data.Fintype.Card

/-!
# Geometric skeleta of the native standard simplex

Adapted from `Quillen/Topology/Realization/SimplexSkeleton.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The support is the native finite support
of the weights. No second simplex model or straightening hypothesis is introduced.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace Convexity.StdSimplex

/-- The geometric `(n - 1)`-skeleton consists of points supported on at most `n` vertices. -/
def skeleton (n d : ℕ) : Set (StdSimplex ℝ (Fin (d + 1))) :=
  {x | x.weights.support.card ≤ n}

@[simp] theorem mem_skeleton {n d : ℕ} (x : StdSimplex ℝ (Fin (d + 1))) :
    x ∈ skeleton n d ↔ x.weights.support.card ≤ n := Iff.rfl

/-- An injective vertex map retains each coordinate at its image vertex. -/
theorem map_apply_of_injective {A B : Type*}
    (α : A → B) (hα : Function.Injective α) (x : StdSimplex ℝ A) (i : A) :
    (x.map α).weights (α i) = x.weights i :=
  Finsupp.mapDomain_apply_of_injective hα x.weights i

/-- A vertex absent from the image has zero coordinate. -/
theorem map_apply_eq_zero_of_not_mem_range {A B : Type*}
    (α : A → B) (x : StdSimplex ℝ A) (j : B) (hj : j ∉ Set.range α) :
    (x.map α).weights j = 0 :=
  Finsupp.mapDomain_of_notMem_range x.weights j hj

/-- Injective vertex maps preserve the number of nonzero coordinates. -/
theorem map_support_card_of_injective {A B : Type*}
    (α : A → B) (hα : Function.Injective α) (x : StdSimplex ℝ A) :
    (x.map α).weights.support.card = x.weights.support.card := by
  classical
  rw [weights_map, Finsupp.mapDomain_support_of_injective hα,
    Finset.card_image_of_injective _ hα]

/-- An injective vertex restriction preserves the geometric skeleton cutoff. -/
theorem map_mem_skeleton_iff {n d e : ℕ} (α : Fin (d + 1) → Fin (e + 1))
    (hα : Function.Injective α) (x : StdSimplex ℝ (Fin (d + 1))) :
    x.map α ∈ skeleton n e ↔ x ∈ skeleton n d := by
  simp only [mem_skeleton, map_support_card_of_injective α hα]

/-- A proper skeleton point has a zero coordinate. -/
theorem skeleton_subset_boundary {n d : ℕ} (hnd : n ≤ d) :
    skeleton n d ⊆ boundary d := by
  classical
  intro x hx
  change x.weights.support.card ≤ n at hx
  change ∃ i, x.weights i = 0
  by_contra h
  have hn : ∀ i, x.weights i ≠ 0 := fun i hi ↦ h ⟨i, hi⟩
  have he : x.weights.support = Finset.univ := by
    ext i
    simp only [Finsupp.mem_support_iff, Finset.mem_univ, iff_true]
    exact hn i
  rw [he, Finset.card_univ, Fintype.card_fin] at hx
  omega

/-- A boundary point has at most `d` nonzero coordinates. -/
theorem boundary_subset_skeleton (d : ℕ) : boundary d ⊆ skeleton d d := by
  classical
  rintro x ⟨i, hi⟩
  have hs : x.weights.support ⊆ Finset.univ.erase i := by
    intro j hj
    have hj0 : x.weights j ≠ 0 := Finsupp.mem_support_iff.mp hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro hji
    subst j
    exact hj0 hi
  have hc := Finset.card_le_card hs
  simpa [mem_skeleton] using hc

/-- The boundary is exactly the highest proper geometric skeleton. -/
theorem boundary_eq_skeleton (d : ℕ) : boundary d = skeleton d d :=
  Set.Subset.antisymm (boundary_subset_skeleton d) (skeleton_subset_boundary le_rfl)

/-- Two distinct vanishing coordinates give the codimension-two skeleton. -/
theorem mem_skeleton_of_two_zero {n : ℕ} (x : StdSimplex ℝ (Fin (n + 2)))
    (i j : Fin (n + 2)) (hij : i ≠ j) (hi : x.weights i = 0) (hj : x.weights j = 0) :
    x ∈ skeleton n (n + 1) := by
  classical
  have hs : x.weights.support ⊆ (Finset.univ.erase i).erase j := by
    intro k hk
    have hk0 : x.weights k ≠ 0 := Finsupp.mem_support_iff.mp hk
    have hki : k ≠ i := by intro h; subst k; exact hk0 hi
    have hkj : k ≠ j := by intro h; subst k; exact hk0 hj
    simpa only [Finset.mem_erase, Finset.mem_univ, and_true] using And.intro hkj hki
  have hc := Finset.card_le_card hs
  simpa [mem_skeleton, Finset.card_erase_of_mem, hij.symm] using hc

end Convexity.StdSimplex
