/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.SphericalFaces
public import Colib.Topology.Realization.SimplexFaceGluing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Filling the ordered tetrahedral horn of spherical triangles

Extracted from `Quillen/Topology/LocalCoefficients/SecondHurewicz.lean`,
lines 220–437, at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The missing face is 1; the included faces are 0, 2, 3. The actual
retraction subtracts the minimum of their coordinates and transfers three
times that amount to vertex 1, using native simplex coordinates.
-/
@[expose] public noncomputable section

open Convexity
open Topology
open scoped BigOperators
universe u

namespace Topology.SphericalHorn

/-- The three included face indices, with the first interior face omitted. -/
def faceIndex (i : Fin 3) : Fin 4 := (1 : Fin 4).succAbove i

/-- The literal geometric horn of the ordered tetrahedron. -/
abbrev Horn := {x : StdSimplex ℝ (Fin 4) // ∃ i : Fin 3, x.weights (faceIndex i) = 0}

/-- Each original included face maps into the actual horn. -/
def face (i : Fin 3) : C(StdSimplex ℝ (Fin 3), Horn) where
  toFun x := ⟨StdSimplex.map (faceIndex i).succAbove x, i,
    StdSimplex.map_succAbove_self (faceIndex i) x⟩
  continuous_toFun := (StdSimplex.continuous_map ℝ _).subtype_mk _

/-- The original finite face cover, retaining all simplex coordinates. -/
def cover : C(Fin 3 × StdSimplex ℝ (Fin 3), Horn) where
  toFun z := face z.1 z.2
  continuous_toFun := continuous_prod_of_discrete_left.mpr (fun i => (face i).continuous)

private theorem cover_surjective : Function.Surjective cover := by
  intro x
  obtain ⟨i, hi⟩ := x.property
  have hm : x.val ∈ Set.range (StdSimplex.map (faceIndex i).succAbove) :=
    (StdSimplex.mem_range_map_succAbove_iff (faceIndex i) x.val).mpr hi
  obtain ⟨a, ha⟩ := hm
  exact ⟨(i, a), Subtype.ext ha⟩

/-- The actual finite compact horn cover is a quotient map. -/
theorem cover_quotient : IsQuotientMap cover :=
  IsQuotientMap.of_surjective_continuous cover_surjective cover.continuous

/-- The smallest coordinate among the three included tetrahedron faces. -/
def mass (x : StdSimplex ℝ (Fin 4)) : ℝ :=
  min (x.weights 0) (min (x.weights 2) (x.weights 3))

/-- The smallest coordinate among the three included tetrahedron faces. -/
theorem mass_nonneg (x : StdSimplex ℝ (Fin 4)) : 0 ≤ mass x :=
  le_min (x.weights_nonneg 0) (le_min (x.weights_nonneg 2) (x.weights_nonneg 3))

/-- The smallest coordinate among the three included tetrahedron faces. -/
theorem mass_le (x : StdSimplex ℝ (Fin 4)) (i : Fin 3) :
    mass x ≤ x.weights (faceIndex i) := by
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- Subtract the smallest included coordinate and transfer the mass to vertex one. -/
def retractPoint (x : StdSimplex ℝ (Fin 4)) : StdSimplex ℝ (Fin 4) :=
  { weights := Finsupp.equivFunOnFinite.symm
      (fun i => if i = 1 then x.weights i + 3 * mass x else x.weights i - mass x)
    nonneg := by
      intro i
      change 0 ≤ if i = 1 then x.weights i + 3 * mass x else x.weights i - mass x
      split_ifs with hi
      · exact add_nonneg (x.weights_nonneg i)
          (mul_nonneg (by norm_num) (mass_nonneg x))
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
        exact sub_nonneg.mpr (mass_le x j)
    total := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      have hx := StdSimplex.total_of_fintype x
      simp only [Fin.sum_univ_succ] at hx ⊢
      change x.weights 0 + (x.weights 1 + (x.weights 2 + (x.weights 3 + 0))) = 1 at hx
      change (x.weights 0 - mass x) + (x.weights 1 + 3 * mass x +
        (x.weights 2 - mass x + (x.weights 3 - mass x + 0))) = 1
      linarith }

private theorem retractPoint_weights (x : StdSimplex ℝ (Fin 4)) (i : Fin 4) :
    (retractPoint x).weights i =
      if i = 1 then x.weights i + 3 * mass x else x.weights i - mass x := rfl

/-- The displayed retraction point lies on one of the three included faces. -/
theorem retractPoint_mem (x : StdSimplex ℝ (Fin 4)) :
    ∃ i : Fin 3, (retractPoint x).weights (faceIndex i) = 0 := by
  by_cases h0 : x.weights 0 ≤ min (x.weights 2) (x.weights 3)
  · refine ⟨0, ?_⟩
    change (retractPoint x).weights 0 = 0
    simp [retractPoint_weights, mass, min_eq_left h0]
  · by_cases h2 : x.weights 2 ≤ x.weights 3
    · refine ⟨1, ?_⟩
      change (retractPoint x).weights 2 = 0
      change x.weights 2 - mass x = 0
      rw [mass, min_eq_right (le_of_not_ge h0), min_eq_left h2, sub_self]
    · refine ⟨2, ?_⟩
      change (retractPoint x).weights 3 = 0
      change x.weights 3 - mass x = 0
      rw [mass, min_eq_right (le_of_not_ge h0), min_eq_right (le_of_not_ge h2), sub_self]

/-- The explicit barycentric retraction is continuous in every coordinate. -/
theorem continuous_retractPoint : Continuous retractPoint := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 4)).continuous_iff]
  apply continuous_pi
  intro i
  change Continuous (fun x : StdSimplex ℝ (Fin 4) =>
    if i = 1 then x.weights i + 3 * mass x else x.weights i - mass x)
  have hm : Continuous mass :=
    (StdSimplex.continuous_weights_apply ℝ 0).min
      ((StdSimplex.continuous_weights_apply ℝ 2).min
        (StdSimplex.continuous_weights_apply ℝ 3))
  split_ifs
  · exact (StdSimplex.continuous_weights_apply ℝ i).add (continuous_const.mul hm)
  · exact (StdSimplex.continuous_weights_apply ℝ i).sub hm

/-- The actual retraction into the included three faces. -/
def retract : C(StdSimplex ℝ (Fin 4), Horn) where
  toFun x := ⟨retractPoint x, retractPoint_mem x⟩
  continuous_toFun := continuous_retractPoint.subtype_mk _

/-- Every point of the original horn is fixed exactly. -/
theorem retract_fixed (x : Horn) : retract x.val = x := by
  have hm : mass x.val = 0 := by
    obtain ⟨i, hi⟩ := x.property
    exact le_antisymm ((mass_le x.val i).trans hi.le) (mass_nonneg x.val)
  apply Subtype.ext
  ext i
  simp [retract, retractPoint_weights, hm]

variable {Y : Type u} [TopologicalSpace Y] {y : Y}

private theorem face_overlap_based (i j : Fin 3) (hij : i ≠ j)
    (a b : StdSimplex ℝ (Fin 3))
    (hab : StdSimplex.map (faceIndex i).succAbove a = StdSimplex.map (faceIndex j).succAbove b) :
    a ∈ StdSimplex.boundary 2 := by
  have hij' : faceIndex j ≠ faceIndex i := by
    intro h
    exact hij (Fin.succAbove_right_injective h.symm)
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij'
  refine ⟨k, ?_⟩
  have hz : (StdSimplex.map (faceIndex i).succAbove a).weights (faceIndex j) = 0 := by
    rw [hab]
    exact StdSimplex.map_succAbove_self (faceIndex j) b
  rw [← hk, StdSimplex.map_apply_injective Fin.succAbove_right_injective] at hz
  exact hz

/-- Evaluate the three original spherical triangles on the finite face cover. -/
def faceValues (a : Fin 3 → SphericalSimplex Y y 2) :
    C(Fin 3 × StdSimplex ℝ (Fin 3), Y) :=
  ⟨fun z => a z.1 z.2,
    continuous_prod_of_discrete_left.mpr (fun i => (a i).val.continuous)⟩

/-- Evaluate the three original spherical triangles on the finite face cover. -/
theorem faceValues_factors (a : Fin 3 → SphericalSimplex Y y 2) :
    Function.FactorsThrough (faceValues a) cover := by
  rintro ⟨i, x⟩ ⟨j, z⟩ h
  have hxz : StdSimplex.map (faceIndex i).succAbove x = StdSimplex.map (faceIndex j).succAbove z :=
    congrArg Subtype.val h
  by_cases hij : i = j
  · subst j
    exact congrArg (a i) (StdSimplex.simplex_map_injective Fin.succAbove_right_injective hxz)
  · exact ((a i).boundary x (face_overlap_based i j hij x z hxz)).trans
      ((a j).boundary z (face_overlap_based j i (fun h => hij h.symm) z x hxz.symm)).symm

/-- Based spherical triangles agree on all actual overlaps of the included faces. -/
def desc (a : Fin 3 → SphericalSimplex Y y 2) : C(Horn, Y) :=
  cover_quotient.lift (faceValues a) (faceValues_factors a)

/-- The descended map restricts to exactly each original spherical triangle. -/
theorem desc_face (a : Fin 3 → SphericalSimplex Y y 2) (i : Fin 3)
    (x : StdSimplex ℝ (Fin 3)) : desc a (face i x) = a i x :=
  ContinuousMap.congr_fun (cover_quotient.lift_comp (faceValues a) (faceValues_factors a)) (i, x)

/-- An actual tetrahedron extending the prescribed three spherical faces. -/
def fill (a : Fin 3 → SphericalSimplex Y y 2) : C(StdSimplex ℝ (Fin 4), Y) :=
  (desc a).comp retract

/-- The extension keeps each included standard face pointwise. -/
theorem fill_face (a : Fin 3 → SphericalSimplex Y y 2) (i : Fin 3)
    (x : StdSimplex ℝ (Fin 3)) :
    fill a (StdSimplex.map (faceIndex i).succAbove x) = a i x := by
  change desc a (retract (face i x).val) = _
  rw [retract_fixed, desc_face]


private theorem skeleton_mem_horn (x : StdSimplex ℝ (Fin 4))
    (hx : x ∈ StdSimplex.skeleton 2 3) : ∃ i : Fin 3, x.weights (faceIndex i) = 0 := by
  classical
  by_contra h
  push Not at h
  have hs : ({0, 2, 3} : Finset (Fin 4)) ⊆ x.weights.support := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact Finsupp.mem_support_iff.mpr (h 0)
    · exact Finsupp.mem_support_iff.mpr (h 1)
    · exact Finsupp.mem_support_iff.mpr (h 2)
  have hc := Finset.card_le_card hs
  have hc3 : ({0, 2, 3} : Finset (Fin 4)).card = 3 := by decide
  rw [hc3] at hc
  change x.weights.support.card ≤ 2 at hx
  omega

/-- Every original edge of the filled tetrahedron remains at the displayed basepoint. -/
theorem fill_skeleton (a : Fin 3 → SphericalSimplex Y y 2)
    (x : StdSimplex ℝ (Fin 4)) (hx : x ∈ StdSimplex.skeleton 2 3) : fill a x = y := by
  obtain ⟨i, hi⟩ := skeleton_mem_horn x hx
  have hm : x ∈ Set.range (StdSimplex.map (faceIndex i).succAbove) :=
    (StdSimplex.mem_range_map_succAbove_iff (faceIndex i) x).mpr hi
  obtain ⟨z, rfl⟩ := hm
  rw [fill_face]
  apply (a i).boundary
  apply StdSimplex.skeleton_subset_boundary (n := 2) (d := 2) le_rfl
  exact (StdSimplex.map_mem_skeleton_iff (faceIndex i).succAbove
    Fin.succAbove_right_injective z).mp hx

/-- The included spherical faces retain their literal original representatives. -/
theorem sphericalFace_fill (a : Fin 3 → SphericalSimplex Y y 2) (i : Fin 3) :
    sphericalFace (fill a) (fill_skeleton a) (faceIndex i) = a i := by
  ext x
  exact fill_face a i x

end Topology.SphericalHorn
