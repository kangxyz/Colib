/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Realization.Prism
public import Colib.Topology.Realization.PrismCoordinates
public import Colib.Analysis.Convex.StdSimplex.FaceCharts

/-! # Topological compatibility of the finite prism charts -/
/-!
Adapted from Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The target uses the pinned native standard simplex and actual Mathlib prism cells.
The implementation retains the source maps, coordinates and universe parameters.
-/
@[expose] public section


noncomputable section

open stdSimplex CategoryTheory MonoidalCategory Opposite
open scoped Simplicial Topology unitInterval

universe u

namespace stdSimplex

/-- Removing the lower duplicate vertex is inverse to collapsing the duplicate pair. -/
theorem face_castSucc_predAbove {n : ℕ} (i : Fin (n + 1))
    (v : _root_.stdSimplex ℝ (Fin (n + 2))) (hv : v i.castSucc = 0) :
    stdSimplex.map i.castSucc.succAbove (stdSimplex.map i.predAbove v) = v := by
  obtain ⟨w, rfl⟩ := (mem_range_map_succAbove_iff i.castSucc v).mpr hv
  rw [stdSimplex.map_comp_apply _ _ w]
  have h : i.predAbove ∘ i.castSucc.succAbove = id := by
    funext j
    exact Fin.predAbove_succAbove i j
  rw [h, stdSimplex.map_id_apply]

/-- Removing the upper duplicate vertex is also inverse to collapsing the pair. -/
theorem face_succ_predAbove {n : ℕ} (i : Fin (n + 1))
    (v : _root_.stdSimplex ℝ (Fin (n + 2))) (hv : v i.succ = 0) :
    stdSimplex.map i.succ.succAbove (stdSimplex.map i.predAbove v) = v := by
  obtain ⟨w, rfl⟩ := (mem_range_map_succAbove_iff i.succ v).mpr hv
  rw [stdSimplex.map_comp_apply _ _ w]
  have h : i.predAbove ∘ i.succ.succAbove = id := by
    funext j
    exact ConcreteCategory.congr_hom (SimplexCategory.δ_comp_σ_succ (i := i)) j
  rw [h, stdSimplex.map_id_apply]

end stdSimplex

namespace SSet

/-- The continuous chart from a closed geometric prism cell to its realization. -/
def realizationPrismLift {n : ℕ} (i : Fin (n + 1)) :
    C(prismCell i, |(Δ[n] ⊗ Δ[1] : SSet.{u})|) where
  toFun z := realizationPrismCell i
    ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm (prismLift i z))
  continuous_toFun := by fun_prop

/-- Each closed-cell chart is a right inverse of the canonical projection. -/
@[simp]
theorem realizationPrismCoordinates_lift {n : ℕ} (i : Fin (n + 1)) (z : prismCell i) :
    realizationPrismCoordinates n (realizationPrismLift.{u} i z) = z.1 := by
  apply Prod.ext
  · exact (realizationPrismCoordinates_cell_fst i _).trans (prismLift_map_predAbove i z)
  · apply Subtype.ext
    exact (realizationPrismCoordinates_cell_snd i _).trans (prismHeight_prismLift i z)

/-- A cell point has exactly the expected barycentric prism coordinates. -/
@[simp]
theorem realizationPrismCoordinates_cell {n : ℕ} (i : Fin (n + 1))
    (v : _root_.stdSimplex ℝ (Fin (n + 2))) :
    realizationPrismCoordinates n (realizationPrismCell.{u} i
      ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm v)) = prismProject i v := by
  apply Prod.ext
  · exact realizationPrismCoordinates_cell_fst i v
  · apply Subtype.ext
    exact realizationPrismCoordinates_cell_snd i v

/-- Adjacent closed-cell charts agree on their overlap. -/
theorem realizationPrismLift_adjacent {n : ℕ} (i : Fin (n + 1))
    {z : _root_.stdSimplex ℝ (Fin (n + 2)) × unitInterval}
    (hi : z ∈ prismCell i.castSucc) (hj : z ∈ prismCell i.succ) :
    realizationPrismLift.{u} i.castSucc ⟨z, hi⟩ =
      realizationPrismLift.{u} i.succ ⟨z, hj⟩ := by
  have hl := face_succ_predAbove i.castSucc (prismLift i.castSucc ⟨z, hi⟩)
    (prismLift_adjacent_left_zero i hi hj)
  have hr := face_castSucc_predAbove i.succ (prismLift i.succ ⟨z, hj⟩)
    (prismLift_adjacent_right_zero i hi hj)
  rw [prismLift_map_predAbove] at hl hr
  change realizationPrismCell i.castSucc ((SimplexCategory.toTopHomeo ⦋n + 2⦌).symm
      (prismLift i.castSucc ⟨z, hi⟩)) =
    realizationPrismCell i.succ ((SimplexCategory.toTopHomeo ⦋n + 2⦌).symm
      (prismLift i.succ ⟨z, hj⟩))
  rw [← hl, ← hr]
  change realizationPrismCell i.castSucc ((SimplexCategory.toTopHomeo ⦋n + 2⦌).symm
      (_root_.stdSimplex.map (SimplexCategory.δ i.castSucc.succ) z.1)) =
    realizationPrismCell i.succ ((SimplexCategory.toTopHomeo ⦋n + 2⦌).symm
      (_root_.stdSimplex.map (SimplexCategory.δ i.succ.castSucc) z.1))
  rw [SimplexCategory.toTopHomeo_symm_naturality_apply,
    SimplexCategory.toTopHomeo_symm_naturality_apply]
  exact ConcreteCategory.congr_hom (realizationPrismCell_adjacent_face i) _

/-- All closed-cell charts agree wherever their domains overlap. -/
theorem realizationPrismLift_overlap {n : ℕ} (i j : Fin (n + 1))
    {z : _root_.stdSimplex ℝ (Fin (n + 1)) × unitInterval}
    (hi : z ∈ prismCell i) (hj : z ∈ prismCell j) :
    realizationPrismLift.{u} i ⟨z, hi⟩ = realizationPrismLift.{u} j ⟨z, hj⟩ := by
  have ordered : ∀ (j i : Fin (n + 1)) (hij : i ≤ j)
      (hi : z ∈ prismCell i) (hj : z ∈ prismCell j),
      realizationPrismLift.{u} i ⟨z, hi⟩ = realizationPrismLift.{u} j ⟨z, hj⟩ := by
    cases n with
    | zero =>
      intro j i hij hi hj
      have h : i = j := Fin.ext (by omega)
      subst j
      rfl
    | succ n =>
      intro j
      induction j using Fin.induction with
      | zero =>
        intro i hij hi hj
        have h : i = 0 := le_antisymm hij (Fin.zero_le i)
        subst i
        rfl
      | succ j ih =>
        intro i hij hi hj
        by_cases heq : i = j.succ
        · subst i
          rfl
        have hij' : i ≤ j.castSucc := by
          simp only [Fin.le_def, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at hij heq ⊢
          omega
        have hk := mem_prismCell_of_between hi hj hij' j.castSucc_le_succ
        exact (ih i hij' hi hk).trans (realizationPrismLift_adjacent j hk hj)
  rcases le_total i j with hij | hji
  · exact ordered j i hij hi hj
  · exact (ordered i j hji hj hi).symm

/-- The standard-prism comparison is surjective. -/
theorem realizationPrismCoordinates_surjective (n : ℕ) :
    Function.Surjective (realizationPrismCoordinates.{u} n) := by
  intro z
  obtain ⟨i, hi⟩ := exists_mem_prismCell z
  exact ⟨realizationPrismLift i ⟨z, hi⟩, realizationPrismCoordinates_lift i ⟨z, hi⟩⟩

/-- The standard-prism comparison is injective: all possible staircase
representatives are identified along their common faces. -/
theorem realizationPrismCoordinates_injective (n : ℕ) :
    Function.Injective (realizationPrismCoordinates.{u} n) := by
  intro x y hxy
  obtain ⟨i, s, rfl⟩ := realizationPrismCell_jointly_surjective x
  obtain ⟨j, t, rfl⟩ := realizationPrismCell_jointly_surjective y
  obtain ⟨v, rfl⟩ := (SimplexCategory.toTopHomeo ⦋n + 1⦌).symm.surjective s
  obtain ⟨w, rfl⟩ := (SimplexCategory.toTopHomeo ⦋n + 1⦌).symm.surjective t
  rw [realizationPrismCoordinates_cell, realizationPrismCoordinates_cell] at hxy
  have hj : prismProject i v ∈ prismCell j := hxy.symm ▸ prismProject_mem_cell j w
  have hp := realizationPrismLift_overlap i j (prismProject_mem_cell i v) hj
  change realizationPrismCell i ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm
      (prismLift i ⟨prismProject i v, prismProject_mem_cell i v⟩)) =
    realizationPrismCell j ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm
      (prismLift j ⟨prismProject i v, hj⟩)) at hp
  rw [prismLift_prismProject] at hp
  have hw : prismLift j ⟨prismProject i v, hj⟩ = w := by
    have hz : (⟨prismProject i v, hj⟩ : prismCell j) =
        ⟨prismProject j w, prismProject_mem_cell j w⟩ := Subtype.ext hxy
    rw [hz, prismLift_prismProject]
  rwa [hw] at hp

/-- The geometric realization of the standard simplicial prism is homeomorphic
to the ordinary topological prism. This is the finite-prism triangulation theorem. -/
def realizationPrismHomeomorph (n : ℕ) :
    |(Δ[n] ⊗ Δ[1] : SSet.{u})| ≃ₜ (_root_.stdSimplex ℝ (Fin (n + 1)) × unitInterval) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (realizationPrismCoordinates n)
      ⟨realizationPrismCoordinates_injective n, realizationPrismCoordinates_surjective n⟩)
    (realizationPrismCoordinates n).continuous

end SSet

attribute [colib_tag "COL-0067",
  colib_ref "HatcherAT" "Section 2.1, proof of Theorem 2.10, prism subdivision, page 112"
    "adaptation" "Finite standard-prism charts and homeomorphism, not general realization products"]
  SSet.realizationPrismHomeomorph
  SSet.realizationPrismLift_overlap
  SSet.realizationPrismCoordinates_injective
  SSet.realizationPrismCoordinates_surjective
