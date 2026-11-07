/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Analysis.Convex.StdSimplex.FaceCharts
public import Mathlib.Topology.UnitInterval
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FunProp

/-!
# Barycentric coordinates for the finite prism triangulation

Adapted from `Quillen/Topology/Realization/PrismCoordinates.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The declarations retain their actual coordinates, maps and hypotheses.
The declarations live with the native `Convexity.StdSimplex` object.
The compactness instance is imported from Mathlib, not reproved here.

These are the native finite-weight coordinates used by Mathlib geometric realization.
-/
@[expose] public section


noncomputable section

open Convexity
open scoped BigOperators unitInterval

namespace Convexity.StdSimplex

/-- The mass strictly above a vertex of a finite simplex. -/
def prismTail {n : ℕ} (w : StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) : ℝ :=
  ∑ j, if i < j then w.weights j else 0

/-- The closed prism cell in which the interval coordinate splits the weight at `i`. -/
def prismCell {n : ℕ} (i : Fin (n + 1)) : Set (StdSimplex ℝ (Fin (n + 1)) × I) :=
  {z | prismTail z.1 i ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ z.1.weights i + prismTail z.1 i}

/-- The amount of weight placed at the lower copy of the split vertex. -/
def prismSplitAmount {n : ℕ} (i : Fin (n + 1))
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : ℝ :=
  z.1.weights i + prismTail z.1 i - (z.2 : ℝ)

lemma prismSplitAmount_nonneg {n : ℕ} (i : Fin (n + 1))
    (z : prismCell i) : 0 ≤ prismSplitAmount i z.1 := by
  exact sub_nonneg.mpr z.2.2

lemma prismSplitAmount_le_weight {n : ℕ} (i : Fin (n + 1))
    (z : prismCell i) : prismSplitAmount i z.1 ≤ z.1.1.weights i := by
  dsimp [prismSplitAmount]
  linarith [z.2.1]

/-- The inverse barycentric coordinate map on one closed prism cell. -/
def prismLift {n : ℕ} (i : Fin (n + 1)) (z : prismCell i) :
    StdSimplex ℝ (Fin (n + 2)) where
  weights := (z.1.1.weights - Finsupp.single i (prismSplitAmount i z.1)).mapDomain
    i.castSucc.succAbove + Finsupp.single i.castSucc (prismSplitAmount i z.1)
  nonneg := by
    apply add_nonneg
    · apply Finsupp.mapDomain_nonneg
      intro j
      by_cases h : j = i
      · subst j
        simpa using sub_nonneg.mpr (prismSplitAmount_le_weight i z)
      · simp [h]
    · exact Finsupp.single_nonneg.mpr (prismSplitAmount_nonneg i z)
  total := by
    simp [Finsupp.sum_add_index, Finsupp.sum_mapDomain_index, Finsupp.sum_sub_index]

/-- Collapsing the two split vertices recovers the original simplex coordinate. -/
@[simp] theorem prismLift_map_predAbove {n : ℕ} (i : Fin (n + 1))
    (z : prismCell i) : (prismLift i z).map i.predAbove = z.1.1 := by
  apply StdSimplex.ext
  simp only [StdSimplex.weights_map, prismLift, Finsupp.mapDomain_add,
    ← Finsupp.mapDomain_comp, Finsupp.mapDomain_single, Fin.predAbove_castSucc_self]
  have h : i.predAbove ∘ i.castSucc.succAbove = id := by
    funext j
    exact Fin.predAbove_succAbove i j
  rw [h, Finsupp.mapDomain_id]
  exact sub_add_cancel _ _

/-- The lower split vertex has exactly the amount removed from the upper copy. -/
@[simp] theorem prismLift_weights_castSucc {n : ℕ} (i : Fin (n + 1))
    (z : prismCell i) : (prismLift i z).weights i.castSucc = prismSplitAmount i z.1 := by
  simp only [prismLift, Finsupp.add_apply, Finsupp.single_eq_same]
  rw [Finsupp.mapDomain_of_notMem_range]
  · exact zero_add _
  · rintro ⟨j, hj⟩
    exact Fin.succAbove_ne _ _ hj

/-- The remaining vertices carry the original weights, with the removed amount
subtracted at the upper copy of the split vertex. -/
@[simp] theorem prismLift_weights_succAbove {n : ℕ} (i : Fin (n + 1))
    (z : prismCell i) (j : Fin (n + 1)) :
    (prismLift i z).weights (i.castSucc.succAbove j) =
      z.1.1.weights j - if j = i then prismSplitAmount i z.1 else 0 := by
  simp [prismLift, Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective,
    Finsupp.single_apply, eq_comm]

/-- The affine interval coordinate on the `i`th prism simplex. -/
def prismHeight {n : ℕ} (i : Fin (n + 1)) (v : StdSimplex ℝ (Fin (n + 2))) : ℝ :=
  ∑ j, if i.castSucc < j then v.weights j else 0

/-- The local inverse recovers the prescribed interval coordinate. -/
@[simp] theorem prismHeight_prismLift {n : ℕ} (i : Fin (n + 1))
    (z : prismCell i) : prismHeight i (prismLift i z) = (z.1.2 : ℝ) := by
  unfold prismHeight
  rw [Fin.sum_univ_succAbove _ i.castSucc]
  simp only [lt_self_iff_false, ↓reduceIte, zero_add,
    Fin.lt_succAbove_iff_le_castSucc, Fin.castSucc_le_castSucc_iff,
    prismLift_weights_succAbove]
  have h : (∑ j : Fin (n + 1), if i ≤ j then
      z.1.1.weights j - if j = i then prismSplitAmount i z.1 else 0 else 0) =
      z.1.1.weights i + prismTail z.1.1 i - prismSplitAmount i z.1 := by
    calc
      _ = ∑ j : Fin (n + 1),
          ((if j = i then z.1.1.weights i - prismSplitAmount i z.1 else 0) +
          (if i < j then z.1.1.weights j else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j = i
        · subst j
          simp
        · by_cases hij : i < j
          · simp [hji, hij, le_of_lt hij]
          · simp [hji, hij, show ¬ i ≤ j by exact fun h ↦ hji (le_antisymm (le_of_not_gt hij) h)]
      _ = _ := by simp [Finset.sum_add_distrib, prismTail]; ring
  rw [h]
  dsimp [prismSplitAmount]
  ring

/-- A nonnegative finite list is crossed by some suffix interval. -/
lemma exists_prism_cut {n : ℕ} (f : Fin (n + 1) → ℝ)
    (hf : ∀ i, 0 ≤ f i) {t : ℝ} (ht : 0 ≤ t) (hT : t ≤ ∑ j, f j) :
    ∃ i, (∑ j, if i < j then f j else 0) ≤ t ∧
      t ≤ f i + ∑ j, if i < j then f j else 0 := by
  induction n with
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · simpa using ht
      · simpa using hT
  | succ n ih =>
      by_cases h : (∑ j : Fin (n + 1), f j.succ) ≤ t
      · refine ⟨0, ?_, ?_⟩
        · simpa [Fin.sum_univ_succ] using h
        · simpa [Fin.sum_univ_succ] using hT
      · obtain ⟨i, hi₁, hi₂⟩ := ih (fun j ↦ f j.succ) (fun j ↦ hf j.succ)
          (le_of_lt (lt_of_not_ge h))
        refine ⟨i.succ, ?_, ?_⟩
        · simpa [Fin.sum_univ_succ] using hi₁
        · simpa [Fin.sum_univ_succ] using hi₂

/-- The finitely many closed prism cells cover the entire product. -/
theorem exists_mem_prismCell {n : ℕ} (z : StdSimplex ℝ (Fin (n + 1)) × I) :
    ∃ i, z ∈ prismCell i := by
  simpa [prismCell, prismTail] using
    exists_prism_cut z.1.weights (fun i ↦ z.1.weights_nonneg i) z.2.2.1
      (show (z.2 : ℝ) ≤ ∑ j, z.1.weights j by simpa using z.2.2.2)

@[fun_prop] theorem continuous_prismTail {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun w : StdSimplex ℝ (Fin (n + 1)) ↦ prismTail w i) := by
  unfold prismTail
  apply continuous_finsetSum
  intro j _
  split_ifs <;> fun_prop

@[fun_prop] theorem continuous_prismSplitAmount {n : ℕ} (i : Fin (n + 1)) :
    Continuous (prismSplitAmount i) := by
  unfold prismSplitAmount
  fun_prop

/-- Each member of the finite prism cover is closed. -/
theorem isClosed_prismCell {n : ℕ} (i : Fin (n + 1)) : IsClosed (prismCell i) := by
  change IsClosed ({z : StdSimplex ℝ (Fin (n + 1)) × I |
    prismTail z.1 i ≤ (z.2 : ℝ)} ∩
    {z : StdSimplex ℝ (Fin (n + 1)) × I |
      (z.2 : ℝ) ≤ z.1.weights i + prismTail z.1 i})
  apply IsClosed.inter <;> apply isClosed_le <;> fun_prop

/-- The barycentric inverse is continuous on its closed cell. -/
@[fun_prop] theorem continuous_prismLift {n : ℕ} (i : Fin (n + 1)) :
    Continuous (prismLift i) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff]
  apply continuous_pi
  intro j
  change Continuous (fun z : prismCell i ↦ (prismLift i z).weights j)
  by_cases hj : j = i.castSucc
  · subst j
    simp only [prismLift_weights_castSucc]
    exact (continuous_prismSplitAmount i).comp continuous_subtype_val
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp only [prismLift_weights_succAbove]
    split_ifs <;> fun_prop

/-- The interval projection on each prism simplex is continuous. -/
@[fun_prop] theorem continuous_prismHeight {n : ℕ} (i : Fin (n + 1)) :
    Continuous (prismHeight i) := by
  unfold prismHeight
  apply continuous_finsetSum
  intro j _
  split_ifs <;> fun_prop

/-- The degeneracy adds the two copies of the split vertex and leaves all other
weights unchanged. -/
theorem prism_map_predAbove_weights {n : ℕ} (i : Fin (n + 1))
    (v : StdSimplex ℝ (Fin (n + 2))) (j : Fin (n + 1)) :
    (v.map i.predAbove).weights j = v.weights (i.castSucc.succAbove j) +
      if j = i then v.weights i.castSucc else 0 := by
  rw [StdSimplex.weights_map, Finsupp.mapDomain_fintype,
    Finsupp.coe_finsetSum, Finset.sum_apply, Fin.sum_univ_succAbove _ i.castSucc]
  simp [Finsupp.single_apply, eq_comm, add_comm]

lemma prism_sum_ge {n : ℕ} (i : Fin (n + 1)) (f : Fin (n + 1) → ℝ) :
    (∑ j, if i ≤ j then f j else 0) = f i + ∑ j, if i < j then f j else 0 := by
  calc
    _ = ∑ j, ((if j = i then f i else 0) + (if i < j then f j else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp
      · by_cases hij : i < j
        · simp [hji, hij, le_of_lt hij]
        · simp [hji, hij, show ¬ i ≤ j by exact fun h ↦ hji (le_antisymm (le_of_not_gt hij) h)]
    _ = _ := by simp [Finset.sum_add_distrib]

/-- The projected height is the strict tail plus the upper split weight. -/
theorem prismHeight_eq_weight_add_tail {n : ℕ} (i : Fin (n + 1))
    (v : StdSimplex ℝ (Fin (n + 2))) :
    prismHeight i v = v.weights i.succ + prismTail (v.map i.predAbove) i := by
  unfold prismHeight
  rw [Fin.sum_univ_succAbove _ i.castSucc]
  simp only [lt_self_iff_false, ↓reduceIte, zero_add,
    Fin.lt_succAbove_iff_le_castSucc, Fin.castSucc_le_castSucc_iff]
  rw [prism_sum_ge]
  simp only [Fin.succAbove_castSucc_self]
  congr 1
  unfold prismTail
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [hij, ↓reduceIte]
    rw [prism_map_predAbove_weights]
    simp [ne_of_gt hij]
  · simp [hij]

lemma prismHeight_nonneg {n : ℕ} (i : Fin (n + 1))
    (v : StdSimplex ℝ (Fin (n + 2))) : 0 ≤ prismHeight i v := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> simp

lemma prismHeight_le_one {n : ℕ} (i : Fin (n + 1))
    (v : StdSimplex ℝ (Fin (n + 2))) : prismHeight i v ≤ 1 := by
  rw [← v.total_of_fintype]
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> simp

/-- The ordinary prism parametrization, in barycentric coordinates. -/
def prismProject {n : ℕ} (i : Fin (n + 1)) (v : StdSimplex ℝ (Fin (n + 2))) :
    StdSimplex ℝ (Fin (n + 1)) × I :=
  (v.map i.predAbove, ⟨prismHeight i v, prismHeight_nonneg i v, prismHeight_le_one i v⟩)

/-- A prism simplex projects into its corresponding closed cell. -/
theorem prismProject_mem_cell {n : ℕ} (i : Fin (n + 1))
    (v : StdSimplex ℝ (Fin (n + 2))) : prismProject i v ∈ prismCell i := by
  change prismTail (v.map i.predAbove) i ≤ prismHeight i v ∧
    prismHeight i v ≤ (v.map i.predAbove).weights i + prismTail (v.map i.predAbove) i
  rw [prismHeight_eq_weight_add_tail, prism_map_predAbove_weights]
  simp only [Fin.succAbove_castSucc_self, ↓reduceIte]
  constructor <;> linarith [v.weights_nonneg i.succ, v.weights_nonneg i.castSucc]

@[simp] theorem prismSplitAmount_prismProject {n : ℕ} (i : Fin (n + 1))
    (v : StdSimplex ℝ (Fin (n + 2))) :
    prismSplitAmount i (prismProject i v) = v.weights i.castSucc := by
  unfold prismSplitAmount prismProject
  simp only [prismHeight_eq_weight_add_tail, prism_map_predAbove_weights,
    Fin.succAbove_castSucc_self, ↓reduceIte]
  ring

/-- The local inverse also recovers every point of its source simplex. -/
@[simp] theorem prismLift_prismProject {n : ℕ} (i : Fin (n + 1))
    (v : StdSimplex ℝ (Fin (n + 2))) :
    prismLift i ⟨prismProject i v, prismProject_mem_cell i v⟩ = v := by
  ext j
  by_cases hj : j = i.castSucc
  · subst j
    simp
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    rw [prismLift_weights_succAbove]
    change (v.map i.predAbove).weights k -
      (if k = i then prismSplitAmount i (prismProject i v) else 0) = _
    rw [prism_map_predAbove_weights, prismSplitAmount_prismProject]
    exact add_sub_cancel_right _ _

/-- The upper endpoint of the cell is the mass on vertices greater than or equal to `i`. -/
lemma prism_weight_add_tail_eq_sum_ge {n : ℕ} (w : StdSimplex ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) : w.weights i + prismTail w i = ∑ j with i ≤ j, w.weights j := by
  rw [Finset.sum_filter, prism_sum_ge]
  rfl

lemma mem_prismCell_iff {n : ℕ} (i : Fin (n + 1))
    (z : StdSimplex ℝ (Fin (n + 1)) × I) : z ∈ prismCell i ↔
      (∑ j with i < j, z.1.weights j) ≤ (z.2 : ℝ) ∧
      (z.2 : ℝ) ≤ ∑ j with i ≤ j, z.1.weights j := by
  simp only [prismCell, Set.mem_ofPred_eq, Finset.sum_filter, prismTail, prism_sum_ge]

/-- The upper duplicate gets the remaining part of the weight at the split vertex. -/
@[simp] theorem prismLift_weights_succ {n : ℕ} (i : Fin (n + 1))
    (z : prismCell i) :
    (prismLift i z).weights i.succ = (z.1.2 : ℝ) - prismTail z.1.1 i := by
  have h := prismLift_weights_succAbove i z i
  simp only [Fin.succAbove_castSucc_self, ↓reduceIte] at h
  rw [h]
  unfold prismSplitAmount
  ring

@[fun_prop] theorem continuous_prismProject {n : ℕ} (i : Fin (n + 1)) :
    Continuous (prismProject i) := by
  unfold prismProject
  fun_prop

/-- The coordinate simplex is homeomorphic to its closed prism cell. -/
def prismCellHomeomorph {n : ℕ} (i : Fin (n + 1)) :
    StdSimplex ℝ (Fin (n + 2)) ≃ₜ prismCell i where
  toFun v := ⟨prismProject i v, prismProject_mem_cell i v⟩
  invFun := prismLift i
  left_inv := prismLift_prismProject i
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact prismLift_map_predAbove i z
    · apply Subtype.ext
      exact prismHeight_prismLift i z
  continuous_toFun := by fun_prop
  continuous_invFun := continuous_prismLift i

/-- The prism parametrization is injective on each individual prism simplex. -/
theorem prismProject_injective {n : ℕ} (i : Fin (n + 1)) :
    Function.Injective (prismProject i) := by
  intro v v' h
  apply (prismCellHomeomorph i).injective
  exact Subtype.ext h

/-- The image of one affine prism parametrization is its closed cell. -/
theorem range_prismProject {n : ℕ} (i : Fin (n + 1)) :
    Set.range (prismProject i) = prismCell i := by
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    exact prismProject_mem_cell i v
  · intro hz
    obtain ⟨v, hv⟩ := (prismCellHomeomorph i).surjective ⟨z, hz⟩
    exact ⟨v, congrArg Subtype.val hv⟩

/-- Moving the cut one vertex to the right removes exactly that vertex's weight. -/
theorem prismTail_castSucc {n : ℕ} (w : StdSimplex ℝ (Fin (n + 2)))
    (i : Fin (n + 1)) :
    prismTail w i.castSucc = w.weights i.succ + prismTail w i.succ := by
  unfold prismTail
  simp only [Fin.castSucc_lt_iff_succ_le]
  exact prism_sum_ge i.succ w.weights

/-- Suffix masses decrease as the cut increases. -/
theorem prismTail_antitone {n : ℕ} (w : StdSimplex ℝ (Fin (n + 1))) :
    Antitone (prismTail w) := by
  intro i j hij
  apply Finset.sum_le_sum
  intro k _
  by_cases hjk : j < k
  · simp [hjk, lt_of_le_of_lt hij hjk]
  · simp only [hjk, ↓reduceIte]
    split_ifs <;> simp

/-- The inclusive suffix masses also decrease with the cut. -/
theorem prismUpper_antitone {n : ℕ} (w : StdSimplex ℝ (Fin (n + 1))) :
    Antitone (fun i ↦ w.weights i + prismTail w i) := by
  intro i j hij
  dsimp only
  rw [prism_weight_add_tail_eq_sum_ge, prism_weight_add_tail_eq_sum_ge]
  simp only [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro k _
  by_cases hjk : j ≤ k
  · simp [hjk, le_trans hij hjk]
  · simp only [hjk, ↓reduceIte]
    split_ifs <;> simp

/-- A point contained in two cells is contained in every cell between them. -/
theorem mem_prismCell_of_between {n : ℕ}
    {z : StdSimplex ℝ (Fin (n + 1)) × I} {i j k : Fin (n + 1)}
    (hi : z ∈ prismCell i) (hj : z ∈ prismCell j) (hik : i ≤ k) (hkj : k ≤ j) :
    z ∈ prismCell k := by
  exact ⟨le_trans (prismTail_antitone z.1 hik) hi.1,
    le_trans hj.2 (prismUpper_antitone z.1 hkj)⟩

/-- Adjacent cells meet exactly at their common suffix-height boundary. -/
theorem prism_adjacent_overlap_height {n : ℕ}
    (i : Fin (n + 1)) {z : StdSimplex ℝ (Fin (n + 2)) × I}
    (hi : z ∈ prismCell i.castSucc) (hj : z ∈ prismCell i.succ) :
    (z.2 : ℝ) = prismTail z.1 i.castSucc := by
  apply le_antisymm
  · simpa only [prismTail_castSucc] using hj.2
  · exact hi.1

/-- On an adjacent-cell overlap, the upper split vertex of the left cell vanishes. -/
theorem prismLift_adjacent_left_zero {n : ℕ}
    (i : Fin (n + 1)) {z : StdSimplex ℝ (Fin (n + 2)) × I}
    (hi : z ∈ prismCell i.castSucc) (hj : z ∈ prismCell i.succ) :
    (prismLift i.castSucc ⟨z, hi⟩).weights i.castSucc.succ = 0 := by
  rw [prismLift_weights_succ]
  exact sub_eq_zero.mpr (prism_adjacent_overlap_height i hi hj)

/-- On an adjacent-cell overlap, the lower split vertex of the right cell vanishes. -/
theorem prismLift_adjacent_right_zero {n : ℕ}
    (i : Fin (n + 1)) {z : StdSimplex ℝ (Fin (n + 2)) × I}
    (hi : z ∈ prismCell i.castSucc) (hj : z ∈ prismCell i.succ) :
    (prismLift i.succ ⟨z, hj⟩).weights i.succ.castSucc = 0 := by
  rw [prismLift_weights_castSucc]
  change z.1.weights i.succ + prismTail z.1 i.succ - (z.2 : ℝ) = 0
  rw [← prismTail_castSucc]
  exact sub_eq_zero.mpr (prism_adjacent_overlap_height i hi hj).symm

end Convexity.StdSimplex

attribute [colib_tag "COL-0065",
  colib_ref "HatcherAT" "Section 2.1, proof of Theorem 2.10, prism subdivision, page 112"
    "adaptation" "Finite prism cells and their coordinate maps, not homology invariance or gluing"]
  Convexity.StdSimplex.prismCellHomeomorph
  Convexity.StdSimplex.exists_mem_prismCell
  Convexity.StdSimplex.isClosed_prismCell
  Convexity.StdSimplex.range_prismProject
  Convexity.StdSimplex.prism_adjacent_overlap_height
  Convexity.StdSimplex.prismLift_adjacent_left_zero
  Convexity.StdSimplex.prismLift_adjacent_right_zero
