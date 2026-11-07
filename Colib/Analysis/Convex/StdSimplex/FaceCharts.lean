/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.Analysis.Convex.StdSimplex.Boundary

/-! # Coordinates of native simplex faces

Direct coordinate proofs for the pinned function-subtype simplex, used for
finite face gluing. Adapted from the face constructions in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

namespace stdSimplex

/-- An injective vertex map preserves each coordinate at its image. -/
theorem map_apply_injective {A B : Type*} [Fintype A] [Fintype B]
    {f : A → B} (hf : Function.Injective f) (x : _root_.stdSimplex ℝ A) (a : A) :
    stdSimplex.map f x (f a) = x a := by
  classical
  change (FunOnFinite.linearMap ℝ ℝ f (x : A → ℝ)) (f a) = _
  simp [FunOnFinite.linearMap_apply_apply, hf.eq_iff, Finset.sum_filter]

/-- The coordinate omitted by an increasing face map is zero. -/
@[simp] theorem map_succAbove_self {d : ℕ} (i : Fin (d + 2))
    (x : _root_.stdSimplex ℝ (Fin (d + 1))) : stdSimplex.map i.succAbove x i = 0 := by
  classical
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove (x : Fin (d + 1) → ℝ)) i = _
  simp [FunOnFinite.linearMap_apply_apply]

/-- Every zero-coordinate point has a native face preimage. -/
theorem mem_range_map_succAbove_iff {d : ℕ} (i : Fin (d + 2))
    (x : _root_.stdSimplex ℝ (Fin (d + 2))) :
    x ∈ Set.range (stdSimplex.map i.succAbove) ↔ x i = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact map_succAbove_self i y
  · intro hx
    let y : _root_.stdSimplex ℝ (Fin (d + 1)) :=
      ⟨fun j ↦ x (i.succAbove j), fun j ↦ stdSimplex.zero_le x _, by
        have h := stdSimplex.sum_eq_one x
        rw [Fin.sum_univ_succAbove (fun j ↦ x j) i, hx, zero_add] at h
        exact h⟩
    refine ⟨y, ?_⟩
    ext j
    by_cases hj : j = i
    · subst j
      exact (map_succAbove_self i y).trans hx.symm
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      exact map_apply_injective Fin.succAbove_right_injective y k

/-- Injective maps of vertices are injective on native simplex points. -/
theorem simplex_map_injective {A B : Type*} [Fintype A] [Fintype B]
    {f : A → B} (hf : Function.Injective f) :
    Function.Injective (stdSimplex.map (S := ℝ) f) := by
  intro x y h
  ext a
  have ha := congrArg (fun z : _root_.stdSimplex ℝ B ↦ z (f a)) h
  simpa only [map_apply_injective hf] using ha

end stdSimplex
