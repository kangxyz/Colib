/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.FaceIntersections

/-! # The original outer cube boundary is a genuine grid face subcomplex

Implementation provenance:
`Quillen/Topology/CubicalSubdivision/OuterBoundary.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision

/-- A face lies on an outer wall when one fixed grid coordinate is an
actual outer endpoint. -/
def OnOuterBoundary {n m : ℕ} (F : FaceIndex n m) : Prop :=
  ∃ i : Fin n, ∃ j : Fin (m+2), F i = Sum.inl j ∧ ((j : ℕ) = 0 ∨ (j : ℕ) = m+1)

theorem face_mem_outerBoundary {n m : ℕ} (F : FaceIndex n m) (hF : OnOuterBoundary F)
    (t : Active F → unitInterval) : face F t ∈ _root_.Cube.boundary (Fin n) := by
  obtain ⟨i,j,hj,hend⟩ := hF
  refine ⟨i,?_⟩
  rw [face_fixed F t i j hj]
  rcases hend with h | h
  · left
    apply Subtype.ext
    change (j : ℝ)/(m+1) = 0
    have hj' : (j : ℝ) = 0 := by exact_mod_cast h
    rw [hj',zero_div]
  · right
    apply Subtype.ext
    change (j : ℝ)/(m+1) = 1
    have hj' : (j : ℝ) = m+1 := by exact_mod_cast h
    rw [hj',div_self (by positivity : (m+1 : ℝ) ≠ 0)]

/-- An interior point can land on the outer cube boundary only if its
entire labeled face is an outer-boundary face. -/
theorem onOuterBoundary_of_interior {n m : ℕ} (F : FaceIndex n m)
    (t : Active F → unitInterval) (ht : t ∉ _root_.Cube.boundary (Active F))
    (hx : face F t ∈ _root_.Cube.boundary (Fin n)) : OnOuterBoundary F := by
  obtain ⟨i,hi⟩ := hx
  have hd : (m+1 : ℝ) ≠ 0 := by positivity
  cases hf : F i with
  | inl j =>
    refine ⟨i,j,hf,?_⟩
    rw [face_fixed F t i j hf] at hi
    rcases hi with h | h
    · left
      have he := congrArg (fun z : unitInterval ↦ (z : ℝ)) h
      change (j : ℝ)/(m+1) = 0 at he
      have hj : (j : ℝ) = 0 := (div_eq_zero_iff.mp he).resolve_right hd
      exact_mod_cast hj
    · right
      have he := congrArg (fun z : unitInterval ↦ (z : ℝ)) h
      change (j : ℝ)/(m+1) = 1 at he
      have hj := (div_eq_one_iff_eq hd).mp he
      exact_mod_cast hj
  | inr k =>
    let a : Active F := ⟨i,k,hf⟩
    rw [face_moving F t i k hf] at hi
    have ha : t a = 0 ∨ t a = 1 := by
      rcases hi with h | h
      · left
        apply Subtype.ext
        have he := congrArg (fun z : unitInterval ↦ (z : ℝ)) h
        change ((k : ℝ)+t a)/(m+1) = 0 at he
        have hz := (div_eq_zero_iff.mp he).resolve_right hd
        change (t a : ℝ) = 0
        have hk : (0 : ℝ) ≤ k := by positivity
        linarith [(t a).2.1]
      · right
        apply Subtype.ext
        have he := congrArg (fun z : unitInterval ↦ (z : ℝ)) h
        change ((k : ℝ)+t a)/(m+1) = 1 at he
        have hz := (div_eq_one_iff_eq hd).mp he
        change (t a : ℝ) = 1
        have hk : (k : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ k.isLt
        linarith [(t a).2.2]
    exact (ht ⟨a,ha⟩).elim

/-- A face not contained in an outer wall meets that wall only on its own
whole original parameter boundary. -/
theorem face_preimage_outerBoundary_subset {n m : ℕ} (F : FaceIndex n m)
    (hF : ¬ OnOuterBoundary F) :
    (face F) ⁻¹' _root_.Cube.boundary (Fin n) ⊆ _root_.Cube.boundary (Active F) := by
  intro t ht
  by_contra hn
  exact hF (onOuterBoundary_of_interior F t hn ht)

/-- Outer-wall faces may be held fixed throughout every skeleton stage. -/
theorem face_preimage_outerBoundary_eq_univ {n m : ℕ} (F : FaceIndex n m)
    (hF : OnOuterBoundary F) : (face F) ⁻¹' _root_.Cube.boundary (Fin n) = Set.univ := by
  ext t
  simp only [Set.mem_preimage,Set.mem_univ,iff_true]
  exact face_mem_outerBoundary F hF t

end Topology.CubicalSubdivision
