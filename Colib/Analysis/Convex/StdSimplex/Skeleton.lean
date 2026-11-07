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
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The support is the finite set of
nonzero coordinates of the actual Mathlib function subtype. No second simplex
model or straightening hypothesis is introduced.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace stdSimplex

attribute [local instance] Classical.propDecidable

/-- The geometric `(n - 1)`-skeleton consists of points supported on at most `n` vertices. -/
def skeleton (n d : ℕ) : Set (_root_.stdSimplex ℝ (Fin (d + 1))) :=
  {x | (Finset.univ.filter fun i ↦ x i ≠ 0).card ≤ n}

@[simp] theorem mem_skeleton {n d : ℕ} (x : _root_.stdSimplex ℝ (Fin (d + 1))) :
    x ∈ skeleton n d ↔ (Finset.univ.filter fun i ↦ x i ≠ 0).card ≤ n := Iff.rfl

/-- An injective vertex map retains each coordinate at its image vertex. -/
theorem map_apply_of_injective {A B : Type*} [Fintype A] [Fintype B]
    (α : A → B) (hα : Function.Injective α) (x : _root_.stdSimplex ℝ A) (i : A) :
    map α x (α i) = x i := by
  classical
  change FunOnFinite.linearMap ℝ ℝ α x (α i) = _
  rw [FunOnFinite.linearMap_apply_apply]
  have h : Finset.univ.filter (fun j ↦ α j = α i) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact hα.eq_iff
  rw [h, Finset.sum_singleton]

/-- A vertex absent from the image has zero coordinate. -/
theorem map_apply_eq_zero_of_not_mem_range {A B : Type*} [Fintype A] [Fintype B]
    (α : A → B) (x : _root_.stdSimplex ℝ A) (j : B) (hj : j ∉ Set.range α) :
    map α x j = 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ α x j = _
  have h : ∀ i, α i ≠ j := fun i hi ↦ hj ⟨i, hi⟩
  simp [FunOnFinite.linearMap_apply_apply, h]

/-- Injective vertex maps preserve the number of nonzero coordinates. -/
theorem map_support_card_of_injective {A B : Type*} [Fintype A] [Fintype B]
    (α : A → B) (hα : Function.Injective α) (x : _root_.stdSimplex ℝ A) :
    (Finset.univ.filter fun j ↦ map α x j ≠ 0).card =
      (Finset.univ.filter fun i ↦ x i ≠ 0).card := by
  classical
  have hs : (Finset.univ.filter fun j ↦ map α x j ≠ 0) =
      (Finset.univ.filter fun i ↦ x i ≠ 0).image α := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hj
      have hr : j ∈ Set.range α := by
        by_contra h
        exact hj (map_apply_eq_zero_of_not_mem_range α x j h)
      obtain ⟨i, rfl⟩ := hr
      exact ⟨i, by simpa only [map_apply_of_injective α hα] using hj, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      simpa only [map_apply_of_injective α hα] using hi
  rw [hs, Finset.card_image_of_injective _ hα]

/-- An injective vertex restriction preserves the geometric skeleton cutoff. -/
theorem map_mem_skeleton_iff {n d e : ℕ} (α : Fin (d + 1) → Fin (e + 1))
    (hα : Function.Injective α) (x : _root_.stdSimplex ℝ (Fin (d + 1))) :
    map α x ∈ skeleton n e ↔ x ∈ skeleton n d := by
  simp only [mem_skeleton, map_support_card_of_injective α hα]

/-- A proper skeleton point has a zero coordinate. -/
theorem skeleton_subset_boundary {n d : ℕ} (hnd : n ≤ d) :
    skeleton n d ⊆ boundary d := by
  classical
  intro x hx
  change (Finset.univ.filter fun i ↦ x i ≠ 0).card ≤ n at hx
  change ∃ i, x i = 0
  by_contra h
  have hn : ∀ i, x i ≠ 0 := fun i hi ↦ h ⟨i, hi⟩
  have he : Finset.univ.filter (fun i ↦ x i ≠ 0) = Finset.univ :=
    Finset.filter_eq_self.mpr (fun i _ ↦ hn i)
  rw [he, Finset.card_univ, Fintype.card_fin] at hx
  omega

/-- A boundary point has at most `d` nonzero coordinates. -/
theorem boundary_subset_skeleton (d : ℕ) : boundary d ⊆ skeleton d d := by
  classical
  rintro x ⟨i, hi⟩
  have hs : (Finset.univ.filter fun j ↦ x j ≠ 0) ⊆ Finset.univ.erase i := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro hji
    subst j
    exact hj hi
  have hc := Finset.card_le_card hs
  simpa [mem_skeleton] using hc

/-- The boundary is exactly the highest proper geometric skeleton. -/
theorem boundary_eq_skeleton (d : ℕ) : boundary d = skeleton d d :=
  Set.Subset.antisymm (boundary_subset_skeleton d) (skeleton_subset_boundary le_rfl)

/-- Two distinct vanishing coordinates give the codimension-two skeleton. -/
theorem mem_skeleton_of_two_zero {n : ℕ} (x : _root_.stdSimplex ℝ (Fin (n + 2)))
    (i j : Fin (n + 2)) (hij : i ≠ j) (hi : x i = 0) (hj : x j = 0) :
    x ∈ skeleton n (n + 1) := by
  classical
  have hs : (Finset.univ.filter fun k ↦ x k ≠ 0) ⊆ (Finset.univ.erase i).erase j := by
    intro k hk
    have hk0 : x k ≠ 0 := (Finset.mem_filter.mp hk).2
    have hki : k ≠ i := by intro h; subst k; exact hk0 hi
    have hkj : k ≠ j := by intro h; subst k; exact hk0 hj
    simpa only [Finset.mem_erase, Finset.mem_univ, and_true] using And.intro hkj hki
  have hc := Finset.card_le_card hs
  simpa [mem_skeleton, Finset.card_erase_of_mem, hij.symm] using hc

end stdSimplex
