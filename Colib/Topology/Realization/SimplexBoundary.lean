/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Tactic.FieldSimp

/-! # Explicit simplex-boundary cylinder retraction

Radial projection away from the point at height two over the barycenter retracts
`Δⁿ × I` onto `(∂Δⁿ × I) ∪ (Δⁿ × {0})`. The formula works in dimension zero.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Topology/Realization/SimplexBoundary.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The coordinate formulae, dimension-zero
case, actual maps, boundary fixation and endpoint conventions are retained.
Only namespace and lower import ownership change. No realization or HEP theorem
is assumed; the finite-weight simplex is the native Mathlib object also used by
PrismCoordinates. Future realization transport uses FiniteSimplexAdapter.
-/
@[expose] public section


noncomputable section

open Convexity
open scoped BigOperators unitInterval

namespace Convexity.StdSimplex

/-- The geometric boundary consists of the points with a zero coordinate. -/
def simplexBoundary (n : ℕ) : Set (StdSimplex ℝ (Fin (n + 1))) :=
  {x | ∃ i, x.weights i = 0}

/-- The side and bottom of the simplex cylinder. -/
def simplexBoundaryCylinder (n : ℕ) : Set (StdSimplex ℝ (Fin (n + 1)) × I) :=
  {z | z.1 ∈ simplexBoundary n ∨ z.2 = 0}

/-- The largest radial barycentric defect. -/
def simplexBoundaryDefect {n : ℕ} (x : StdSimplex ℝ (Fin (n + 1))) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i ↦ 1 - (n + 1 : ℝ) * x.weights i)

lemma le_simplexBoundaryDefect {n : ℕ} (x : StdSimplex ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) : 1 - (n + 1 : ℝ) * x.weights i ≤ simplexBoundaryDefect x :=
  Finset.le_sup' (fun j ↦ 1 - (n + 1 : ℝ) * x.weights j) (Finset.mem_univ i)

lemma simplexBoundaryDefect_le_one {n : ℕ} (x : StdSimplex ℝ (Fin (n + 1))) :
    simplexBoundaryDefect x ≤ 1 := by
  apply Finset.sup'_le
  intro i _
  have := x.weights_nonneg i
  have hn : 0 ≤ (n + 1 : ℝ) := by positivity
  nlinarith

lemma exists_simplexBoundaryDefect_eq {n : ℕ} (x : StdSimplex ℝ (Fin (n + 1))) :
    ∃ i, simplexBoundaryDefect x = 1 - (n + 1 : ℝ) * x.weights i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i : Fin (n + 1) ↦ 1 - (n + 1 : ℝ) * x.weights i)
  exact ⟨i, hi⟩

@[fun_prop] theorem continuous_simplexBoundaryDefect {n : ℕ} :
    Continuous (simplexBoundaryDefect (n := n)) := by
  apply Continuous.finset_sup'_apply
  intro i _
  fun_prop

/-- The reciprocal radial expansion factor. Its lower bound is `1/2`. -/
def simplexBoundaryScale {n : ℕ} (z : StdSimplex ℝ (Fin (n + 1)) × I) : ℝ :=
  max (1 - (z.2 : ℝ) / 2) (simplexBoundaryDefect z.1)

lemma half_le_simplexBoundaryScale {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : 1 / 2 ≤ simplexBoundaryScale z := by
  have ht := z.2.2.2
  have := le_max_left (1 - (z.2 : ℝ) / 2) (simplexBoundaryDefect z.1)
  dsimp [simplexBoundaryScale]
  linarith

lemma simplexBoundaryScale_pos {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : 0 < simplexBoundaryScale z :=
  lt_of_lt_of_le (by norm_num) (half_le_simplexBoundaryScale z)

lemma simplexBoundaryScale_ne_zero {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : simplexBoundaryScale z ≠ 0 :=
  ne_of_gt (simplexBoundaryScale_pos z)

lemma simplexBoundaryScale_le_one {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : simplexBoundaryScale z ≤ 1 := by
  apply max_le
  · have := z.2.2.1
    linarith
  · exact simplexBoundaryDefect_le_one z.1

lemma one_sub_height_le_simplexBoundaryScale {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) :
    1 - (z.2 : ℝ) / 2 ≤ simplexBoundaryScale z := le_max_left _ _

lemma defect_le_simplexBoundaryScale {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) :
    simplexBoundaryDefect z.1 ≤ simplexBoundaryScale z := le_max_right _ _

@[fun_prop] theorem continuous_simplexBoundaryScale {n : ℕ} :
    Continuous (simplexBoundaryScale (n := n)) := by
  unfold simplexBoundaryScale
  fun_prop

/-- The barycentric coordinates of the radial projection. -/
def simplexBoundaryRetractWeight {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) (i : Fin (n + 1)) : ℝ :=
  ((n + 1 : ℝ) * z.1.weights i + simplexBoundaryScale z - 1) /
    ((n + 1 : ℝ) * simplexBoundaryScale z)

lemma simplexBoundaryRetractWeight_nonneg {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) (i : Fin (n + 1)) :
    0 ≤ simplexBoundaryRetractWeight z i := by
  apply div_nonneg
  · have := (le_simplexBoundaryDefect z.1 i).trans (defect_le_simplexBoundaryScale z)
    linarith
  · exact le_of_lt (mul_pos (by positivity) (simplexBoundaryScale_pos z))

lemma sum_simplexBoundaryRetractWeight {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) :
    ∑ i, simplexBoundaryRetractWeight z i = 1 := by
  unfold simplexBoundaryRetractWeight
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    StdSimplex.total_of_fintype, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [simplexBoundaryScale_ne_zero z]
  ring

/-- The simplex component of radial projection. -/
def simplexBoundaryRetractPoint {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : StdSimplex ℝ (Fin (n + 1)) where
  weights := Finsupp.equivFunOnFinite.symm (simplexBoundaryRetractWeight z)
  nonneg i := simplexBoundaryRetractWeight_nonneg z i
  total := by
    simpa [Finsupp.sum_fintype] using sum_simplexBoundaryRetractWeight z

@[simp] lemma simplexBoundaryRetractPoint_weights {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) (i : Fin (n + 1)) :
    (simplexBoundaryRetractPoint z).weights i = simplexBoundaryRetractWeight z i := rfl

/-- The height of radial projection. -/
def simplexBoundaryRetractHeight {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : ℝ :=
  2 + ((z.2 : ℝ) - 2) / simplexBoundaryScale z

lemma simplexBoundaryRetractHeight_nonneg {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : 0 ≤ simplexBoundaryRetractHeight z := by
  have hd := simplexBoundaryScale_pos z
  have ht := one_sub_height_le_simplexBoundaryScale z
  unfold simplexBoundaryRetractHeight
  have h : -(2 : ℝ) ≤ ((z.2 : ℝ) - 2) / simplexBoundaryScale z := by
    apply (le_div_iff₀ hd).mpr
    linarith
  linarith

lemma simplexBoundaryRetractHeight_le_one {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : simplexBoundaryRetractHeight z ≤ 1 := by
  have hd := simplexBoundaryScale_pos z
  have hu := simplexBoundaryScale_le_one z
  have ht := z.2.2.2
  unfold simplexBoundaryRetractHeight
  have h : ((z.2 : ℝ) - 2) / simplexBoundaryScale z ≤ -(1 : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    linarith
  linarith

/-- Explicit radial projection onto the side and bottom of the simplex cylinder. -/
def simplexBoundaryRetract {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : StdSimplex ℝ (Fin (n + 1)) × I :=
  (simplexBoundaryRetractPoint z, ⟨simplexBoundaryRetractHeight z,
    simplexBoundaryRetractHeight_nonneg z, simplexBoundaryRetractHeight_le_one z⟩)

@[fun_prop] theorem continuous_simplexBoundaryRetractWeight {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun z : StdSimplex ℝ (Fin (n + 1)) × I ↦ simplexBoundaryRetractWeight z i) := by
  unfold simplexBoundaryRetractWeight
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    exact mul_ne_zero (by positivity) (simplexBoundaryScale_ne_zero z)

@[fun_prop] theorem continuous_simplexBoundaryRetractPoint {n : ℕ} :
    Continuous (simplexBoundaryRetractPoint (n := n)) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff]
  apply continuous_pi
  exact continuous_simplexBoundaryRetractWeight

@[fun_prop] theorem continuous_simplexBoundaryRetractHeight {n : ℕ} :
    Continuous (simplexBoundaryRetractHeight (n := n)) := by
  unfold simplexBoundaryRetractHeight
  apply Continuous.add continuous_const
  apply Continuous.div
  · fun_prop
  · fun_prop
  · exact simplexBoundaryScale_ne_zero

@[fun_prop] theorem continuous_simplexBoundaryRetract {n : ℕ} :
    Continuous (simplexBoundaryRetract (n := n)) := by
  unfold simplexBoundaryRetract
  fun_prop

/-- Every point projects either to the bottom or to a zero barycentric coordinate. -/
theorem simplexBoundaryRetract_mem {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) :
    simplexBoundaryRetract z ∈ simplexBoundaryCylinder n := by
  rcases le_total (simplexBoundaryDefect z.1) (1 - (z.2 : ℝ) / 2) with h | h
  · right
    apply Subtype.ext
    change simplexBoundaryRetractHeight z = 0
    have he : simplexBoundaryScale z = 1 - (z.2 : ℝ) / 2 := max_eq_left h
    unfold simplexBoundaryRetractHeight
    have hdiv : ((z.2 : ℝ) - 2) / simplexBoundaryScale z = -2 := by
      apply (div_eq_iff (simplexBoundaryScale_ne_zero z)).mpr
      rw [he]
      ring
    linarith
  · left
    obtain ⟨i, hi⟩ := exists_simplexBoundaryDefect_eq z.1
    refine ⟨i, ?_⟩
    change simplexBoundaryRetractWeight z i = 0
    have he : simplexBoundaryScale z = simplexBoundaryDefect z.1 := max_eq_right h
    simp only [simplexBoundaryRetractWeight, he, hi]
    convert zero_div ((n + 1 : ℝ) * (1 - (n + 1 : ℝ) * z.1.weights i)) using 1
    ring

lemma simplexBoundaryScale_eq_one {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) (hz : z ∈ simplexBoundaryCylinder n) :
    simplexBoundaryScale z = 1 := by
  apply le_antisymm (simplexBoundaryScale_le_one z)
  rcases hz with ⟨i, hi⟩ | ht
  · have := (le_simplexBoundaryDefect z.1 i).trans (defect_le_simplexBoundaryScale z)
    simpa [hi] using this
  · have := one_sub_height_le_simplexBoundaryScale z
    simpa [ht] using this

/-- Radial projection is the identity on the side and bottom. -/
theorem simplexBoundaryRetract_eq_self {n : ℕ}
    (z : StdSimplex ℝ (Fin (n + 1)) × I) (hz : z ∈ simplexBoundaryCylinder n) :
    simplexBoundaryRetract z = z := by
  have hd := simplexBoundaryScale_eq_one z hz
  apply Prod.ext
  · apply StdSimplex.ext
    ext i
    change simplexBoundaryRetractWeight z i = z.1.weights i
    simp only [simplexBoundaryRetractWeight, hd, add_sub_cancel_right, mul_one]
    exact mul_div_cancel_left₀ _ (by positivity)
  · apply Subtype.ext
    change simplexBoundaryRetractHeight z = (z.2 : ℝ)
    simp [simplexBoundaryRetractHeight, hd]

/-- The boundary is closed, since it is a finite union of zero-coordinate faces. -/
theorem isClosed_simplexBoundary (n : ℕ) : IsClosed (simplexBoundary n) := by
  simp only [simplexBoundary, Set.ofPred_exists]
  apply isClosed_iUnion_of_finite
  intro i
  exact isClosed_eq (StdSimplex.continuous_weights_apply ℝ i) continuous_const

/-- The side-bottom union is closed in the simplex cylinder. -/
theorem isClosed_simplexBoundaryCylinder (n : ℕ) : IsClosed (simplexBoundaryCylinder n) :=
  ((isClosed_simplexBoundary n).preimage continuous_fst).union
    (isClosed_eq continuous_snd continuous_const)

/-- The explicit continuous retraction, with the restricted codomain. -/
def simplexBoundaryCylinderRetraction (n : ℕ) :
    C(StdSimplex ℝ (Fin (n + 1)) × I, simplexBoundaryCylinder n) where
  toFun z := ⟨simplexBoundaryRetract z, simplexBoundaryRetract_mem z⟩
  continuous_toFun := continuous_simplexBoundaryRetract.subtype_mk _

@[simp] theorem simplexBoundaryCylinderRetraction_coe (n : ℕ)
    (z : simplexBoundaryCylinder n) : simplexBoundaryCylinderRetraction n z = z := by
  apply Subtype.ext
  exact simplexBoundaryRetract_eq_self z.1 z.2

end Convexity.StdSimplex

attribute [colib_tag "COL-0098",
  colib_ref "HatcherAT" "Chapter 0, proof of Proposition 0.16, page 15"
    "adaptation"
    "Radial cylinder retraction in finite simplex coordinates, not the full CW-pair theorem"]
  Convexity.StdSimplex.simplexBoundaryCylinderRetraction
  Convexity.StdSimplex.simplexBoundaryCylinderRetraction_coe
  Convexity.StdSimplex.simplexBoundaryRetract_mem
  Convexity.StdSimplex.simplexBoundaryRetract_eq_self
