/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.Topology.Homotopy.Equiv
public import Colib.Topology.Realization.SimplexBoundary

/-!
# A genuine open collar of the geometric simplex boundary

The barycentric defect cuts out an open neighborhood of the boundary. The
already constructed cylinder retraction deforms this neighborhood onto the
boundary, fixes the boundary at all times, and stays in the neighborhood.
This is the local geometric input for skeletal path approximation; unlike the
closed image of a characteristic simplex, the collar really is open.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Topology/Realization/EdgePathPresentation/Collar.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The coordinate formulae, dimension-zero
case, actual maps, boundary fixation and endpoint conventions are retained.
Only namespace and lower import ownership change. No realization or HEP theorem
is assumed; the finite-weight simplex is the native Mathlib object also used by
PrismCoordinates. Future realization transport uses FiniteSimplexAdapter.
-/
@[expose] public section


noncomputable section

open Convexity Set
open scoped Topology unitInterval

namespace Convexity.StdSimplex

/-- A point is on the boundary exactly when its barycentric defect is one. -/
theorem simplexBoundaryDefect_eq_one_iff {n : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) :
    simplexBoundaryDefect x = 1 ↔ x ∈ simplexBoundary n := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_simplexBoundaryDefect_eq x
    refine ⟨i, ?_⟩
    have hn : 0 < (n + 1 : ℝ) := by positivity
    rw [h] at hi
    nlinarith
  · rintro ⟨i, hi⟩
    apply le_antisymm (simplexBoundaryDefect_le_one x)
    simpa [hi] using le_simplexBoundaryDefect x i

/-- The outer half of the simplex in barycentric radial coordinates. -/
def simplexBoundaryCollar (n : ℕ) : Set (StdSimplex ℝ (Fin (n + 1))) :=
  {x | (1 : ℝ) / 2 < simplexBoundaryDefect x}

/-- The collar is open in the whole geometric simplex. -/
theorem isOpen_simplexBoundaryCollar (n : ℕ) : IsOpen (simplexBoundaryCollar n) :=
  isOpen_lt continuous_const continuous_simplexBoundaryDefect

/-- The entire geometric boundary lies in the open collar. -/
theorem simplexBoundary_subset_collar (n : ℕ) :
    simplexBoundary n ⊆ simplexBoundaryCollar n := by
  intro x hx
  change (1 : ℝ) / 2 < simplexBoundaryDefect x
  rw [(simplexBoundaryDefect_eq_one_iff x).mpr hx]
  norm_num

/-- Radial expansion cannot decrease a nonnegative barycentric defect. -/
theorem simplexBoundaryDefect_le_retractPoint {n : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (t : unitInterval)
    (hx : 0 ≤ simplexBoundaryDefect x) :
    simplexBoundaryDefect x ≤ simplexBoundaryDefect (simplexBoundaryRetractPoint (x, t)) := by
  obtain ⟨i, hi⟩ := exists_simplexBoundaryDefect_eq x
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hs := simplexBoundaryScale_pos (x, t)
  have hs1 := simplexBoundaryScale_le_one (x, t)
  have hcalc :
      1 - (n + 1 : ℝ) * (simplexBoundaryRetractPoint (x, t)).weights i =
        simplexBoundaryDefect x / simplexBoundaryScale (x, t) := by
    rw [simplexBoundaryRetractPoint_weights]
    unfold simplexBoundaryRetractWeight
    rw [hi]
    field_simp [hn, ne_of_gt hs]
    ring
  apply le_trans _ (le_simplexBoundaryDefect (simplexBoundaryRetractPoint (x, t)) i)
  rw [hcalc]
  exact (le_div_iff₀ hs).mpr (mul_le_of_le_one_right hx hs1)

/-- The cylinder retraction preserves the open collar at every time. -/
theorem simplexBoundaryRetractPoint_mem_collar {n : ℕ}
    (x : simplexBoundaryCollar n) (t : unitInterval) :
    simplexBoundaryRetractPoint (x.1, t) ∈ simplexBoundaryCollar n := by
  exact lt_of_lt_of_le x.2
    (simplexBoundaryDefect_le_retractPoint x.1 t (le_of_lt (lt_trans (by norm_num) x.2)))

/-- At time one, every collar point has reached the boundary. -/
theorem simplexBoundaryRetractPoint_one_mem_boundary {n : ℕ}
    (x : simplexBoundaryCollar n) :
    simplexBoundaryRetractPoint (x.1, 1) ∈ simplexBoundary n := by
  obtain ⟨i, hi⟩ := exists_simplexBoundaryDefect_eq x.1
  refine ⟨i, ?_⟩
  have hs : simplexBoundaryScale (x.1, 1) = simplexBoundaryDefect x.1 := by
    unfold simplexBoundaryScale
    apply max_eq_right
    change 1 - (1 : ℝ) / 2 ≤ simplexBoundaryDefect x.1
    have hx : (1 : ℝ) / 2 < simplexBoundaryDefect x.1 := x.2
    linarith
  rw [simplexBoundaryRetractPoint_weights]
  unfold simplexBoundaryRetractWeight
  rw [hs, hi]
  have hnum : (n + 1 : ℝ) * x.1.weights i +
      (1 - (n + 1 : ℝ) * x.1.weights i) - 1 = 0 := by ring
  rw [hnum, zero_div]

/-- The cylinder retraction starts at the original point. -/
@[simp] theorem simplexBoundaryRetractPoint_zero {n : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) :
    simplexBoundaryRetractPoint (x, 0) = x :=
  congrArg Prod.fst (simplexBoundaryRetract_eq_self (x, 0) (Or.inr rfl))

/-- The cylinder retraction fixes every boundary point at all times. -/
@[simp] theorem simplexBoundaryRetractPoint_boundary {n : ℕ}
    (x : simplexBoundary n) (t : unitInterval) :
    simplexBoundaryRetractPoint (x.1, t) = x.1 :=
  congrArg Prod.fst (simplexBoundaryRetract_eq_self (x.1, t) (Or.inl x.2))

/-- The boundary inclusion into its open collar. -/
def simplexBoundaryCollarInclusion (n : ℕ) :
    C(simplexBoundary n, simplexBoundaryCollar n) where
  toFun x := ⟨x.1, simplexBoundary_subset_collar n x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The collar retracts continuously onto the geometric boundary. -/
def simplexBoundaryCollarRetraction (n : ℕ) :
    C(simplexBoundaryCollar n, simplexBoundary n) where
  toFun x := ⟨simplexBoundaryRetractPoint (x.1, 1),
    simplexBoundaryRetractPoint_one_mem_boundary x⟩
  continuous_toFun := (continuous_simplexBoundaryRetractPoint.comp
    (continuous_subtype_val.prodMk continuous_const)).subtype_mk _

@[simp] theorem simplexBoundaryCollarRetraction_inclusion (n : ℕ)
    (x : simplexBoundary n) :
    simplexBoundaryCollarRetraction n (simplexBoundaryCollarInclusion n x) = x := by
  apply Subtype.ext
  exact simplexBoundaryRetractPoint_boundary x 1

/-- The radial homotopy stays in the open collar and fixes the boundary. -/
def simplexBoundaryCollarHomotopy (n : ℕ) :
    (ContinuousMap.id (simplexBoundaryCollar n)).HomotopyRel
      ((simplexBoundaryCollarInclusion n).comp (simplexBoundaryCollarRetraction n))
      (Set.range (simplexBoundaryCollarInclusion n)) where
  toFun z := ⟨simplexBoundaryRetractPoint (z.2.1, z.1),
    simplexBoundaryRetractPoint_mem_collar z.2 z.1⟩
  continuous_toFun := (continuous_simplexBoundaryRetractPoint.comp
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)).subtype_mk _
  map_zero_left x := Subtype.ext (simplexBoundaryRetractPoint_zero x.1)
  map_one_left _ := rfl
  prop' t _ hx := by
    obtain ⟨x, rfl⟩ := hx
    apply Subtype.ext
    exact simplexBoundaryRetractPoint_boundary x t

/-- The open collar is genuinely homotopy equivalent to the boundary, with
forward map exactly its inclusion. -/
def simplexBoundaryCollarHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (simplexBoundary n) (simplexBoundaryCollar n) where
  toFun := simplexBoundaryCollarInclusion n
  invFun := simplexBoundaryCollarRetraction n
  left_inv := by
    have h : (simplexBoundaryCollarRetraction n).comp (simplexBoundaryCollarInclusion n) =
        ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      exact simplexBoundaryCollarRetraction_inclusion n x
    rw [h]
  right_inv := ⟨(simplexBoundaryCollarHomotopy n).toHomotopy.symm⟩

end Convexity.StdSimplex

attribute [colib_tag "COL-0099",
  colib_ref "HatcherAT" "Chapter 0, proof of Proposition 0.16, page 15"
    "background"
    "Radial construction for the explicit open collar, fixing the entire boundary"]
  Convexity.StdSimplex.isOpen_simplexBoundaryCollar
  Convexity.StdSimplex.simplexBoundary_subset_collar
  Convexity.StdSimplex.simplexBoundaryCollarRetraction
  Convexity.StdSimplex.simplexBoundaryCollarHomotopy
  Convexity.StdSimplex.simplexBoundaryCollarHomotopyEquiv
