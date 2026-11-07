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
open Topology
open scoped BigOperators
universe u

namespace Topology.SphericalHorn

/-- The three included face indices, with the first interior face omitted. -/
def faceIndex (i : Fin 3) : Fin 4 := (1 : Fin 4).succAbove i

/-- The literal geometric horn of the ordered tetrahedron. -/
abbrev Horn := {x : _root_.stdSimplex ℝ (Fin 4) // ∃ i : Fin 3, x (faceIndex i) = 0}

/-- Each original included face maps into the actual horn. -/
def face (i : Fin 3) : C(_root_.stdSimplex ℝ (Fin 3), Horn) where
  toFun x := ⟨stdSimplex.map (faceIndex i).succAbove x, i,
    stdSimplex.map_succAbove_self (faceIndex i) x⟩
  continuous_toFun := (stdSimplex.continuous_map _).subtype_mk _

/-- The original finite face cover, retaining all simplex coordinates. -/
def cover : C(Fin 3 × _root_.stdSimplex ℝ (Fin 3), Horn) where
  toFun z := face z.1 z.2
  continuous_toFun := continuous_prod_of_discrete_left.mpr (fun i => (face i).continuous)

private theorem cover_surjective : Function.Surjective cover := by
  intro x
  obtain ⟨i, hi⟩ := x.property
  have hm : x.val ∈ Set.range (stdSimplex.map (faceIndex i).succAbove) :=
    (stdSimplex.mem_range_map_succAbove_iff (faceIndex i) x.val).mpr hi
  obtain ⟨a, ha⟩ := hm
  exact ⟨(i, a), Subtype.ext ha⟩

/-- The actual finite compact horn cover is a quotient map. -/
theorem cover_quotient : IsQuotientMap cover :=
  IsQuotientMap.of_surjective_continuous cover_surjective cover.continuous

/-- The smallest coordinate among the three included tetrahedron faces. -/
def mass (x : _root_.stdSimplex ℝ (Fin 4)) : ℝ :=
  min (x 0) (min (x 2) (x 3))

/-- The smallest coordinate among the three included tetrahedron faces. -/
theorem mass_nonneg (x : _root_.stdSimplex ℝ (Fin 4)) : 0 ≤ mass x :=
  le_min (stdSimplex.zero_le x 0) (le_min (stdSimplex.zero_le x 2) (stdSimplex.zero_le x 3))

/-- The smallest coordinate among the three included tetrahedron faces. -/
theorem mass_le (x : _root_.stdSimplex ℝ (Fin 4)) (i : Fin 3) :
    mass x ≤ x (faceIndex i) := by
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- Subtract the smallest included coordinate and transfer the mass to vertex one. -/
def retractPoint (x : _root_.stdSimplex ℝ (Fin 4)) : _root_.stdSimplex ℝ (Fin 4) :=
  ⟨(fun i => if i = 1 then x i + 3 * mass x else x i - mass x),
    (by
      intro i
      dsimp only
      split_ifs with hi
      · exact add_nonneg (stdSimplex.zero_le x i)
          (mul_nonneg (by norm_num) (mass_nonneg x))
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
        exact sub_nonneg.mpr (mass_le x j)),
    (by
      have hx := stdSimplex.sum_eq_one x
      simp only [Fin.sum_univ_succ] at hx ⊢
      change x 0 + (x 1 + (x 2 + (x 3 + 0))) = 1 at hx
      change (x 0 - mass x) + (x 1 + 3 * mass x +
        (x 2 - mass x + (x 3 - mass x + 0))) = 1
      linarith)⟩

private theorem retractPoint_weights (x : _root_.stdSimplex ℝ (Fin 4)) (i : Fin 4) :
    retractPoint x i = if i = 1 then x i + 3 * mass x else x i - mass x := rfl

/-- The displayed retraction point lies on one of the three included faces. -/
theorem retractPoint_mem (x : _root_.stdSimplex ℝ (Fin 4)) :
    ∃ i : Fin 3, (retractPoint x) (faceIndex i) = 0 := by
  by_cases h0 : x 0 ≤ min (x 2) (x 3)
  · refine ⟨0, ?_⟩
    change (retractPoint x) 0 = 0
    simp [retractPoint_weights, mass, min_eq_left h0]
  · by_cases h2 : x 2 ≤ x 3
    · refine ⟨1, ?_⟩
      change (retractPoint x) 2 = 0
      change x 2 - mass x = 0
      rw [mass, min_eq_right (le_of_not_ge h0), min_eq_left h2, sub_self]
    · refine ⟨2, ?_⟩
      change (retractPoint x) 3 = 0
      change x 3 - mass x = 0
      rw [mass, min_eq_right (le_of_not_ge h0), min_eq_right (le_of_not_ge h2), sub_self]

/-- The explicit barycentric retraction is continuous in every coordinate. -/
theorem continuous_retractPoint : Continuous retractPoint := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  change Continuous (fun x : _root_.stdSimplex ℝ (Fin 4) =>
    if i = 1 then x i + 3 * mass x else x i - mass x)
  have hm : Continuous mass :=
    ((continuous_apply 0).comp continuous_subtype_val).min
      (((continuous_apply 2).comp continuous_subtype_val).min
        ((continuous_apply 3).comp continuous_subtype_val))
  split_ifs
  · exact ((continuous_apply i).comp continuous_subtype_val).add (continuous_const.mul hm)
  · exact ((continuous_apply i).comp continuous_subtype_val).sub hm

/-- The actual retraction into the included three faces. -/
def retract : C(_root_.stdSimplex ℝ (Fin 4), Horn) where
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
    (a b : _root_.stdSimplex ℝ (Fin 3))
    (hab : stdSimplex.map (faceIndex i).succAbove a = stdSimplex.map (faceIndex j).succAbove b) :
    a ∈ stdSimplex.boundary 2 := by
  have hij' : faceIndex j ≠ faceIndex i := by
    intro h
    exact hij (Fin.succAbove_right_injective h.symm)
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij'
  refine ⟨k, ?_⟩
  have hz : stdSimplex.map (faceIndex i).succAbove a (faceIndex j) = 0 := by
    rw [hab]
    exact stdSimplex.map_succAbove_self (faceIndex j) b
  rw [← hk, stdSimplex.map_apply_injective Fin.succAbove_right_injective] at hz
  exact hz

/-- Evaluate the three original spherical triangles on the finite face cover. -/
def faceValues (a : Fin 3 → SphericalSimplex Y y 2) :
    C(Fin 3 × _root_.stdSimplex ℝ (Fin 3), Y) :=
  ⟨fun z => a z.1 z.2,
    continuous_prod_of_discrete_left.mpr (fun i => (a i).val.continuous)⟩

/-- Evaluate the three original spherical triangles on the finite face cover. -/
theorem faceValues_factors (a : Fin 3 → SphericalSimplex Y y 2) :
    Function.FactorsThrough (faceValues a) cover := by
  rintro ⟨i, x⟩ ⟨j, z⟩ h
  have hxz : stdSimplex.map (faceIndex i).succAbove x = stdSimplex.map (faceIndex j).succAbove z :=
    congrArg Subtype.val h
  by_cases hij : i = j
  · subst j
    exact congrArg (a i) (stdSimplex.simplex_map_injective Fin.succAbove_right_injective hxz)
  · exact ((a i).boundary x (face_overlap_based i j hij x z hxz)).trans
      ((a j).boundary z (face_overlap_based j i (fun h => hij h.symm) z x hxz.symm)).symm

/-- Based spherical triangles agree on all actual overlaps of the included faces. -/
def desc (a : Fin 3 → SphericalSimplex Y y 2) : C(Horn, Y) :=
  cover_quotient.lift (faceValues a) (faceValues_factors a)

/-- The descended map restricts to exactly each original spherical triangle. -/
theorem desc_face (a : Fin 3 → SphericalSimplex Y y 2) (i : Fin 3)
    (x : _root_.stdSimplex ℝ (Fin 3)) : desc a (face i x) = a i x :=
  ContinuousMap.congr_fun (cover_quotient.lift_comp (faceValues a) (faceValues_factors a)) (i, x)

/-- An actual tetrahedron extending the prescribed three spherical faces. -/
def fill (a : Fin 3 → SphericalSimplex Y y 2) : C(_root_.stdSimplex ℝ (Fin 4), Y) :=
  (desc a).comp retract

/-- The extension keeps each included standard face pointwise. -/
theorem fill_face (a : Fin 3 → SphericalSimplex Y y 2) (i : Fin 3)
    (x : _root_.stdSimplex ℝ (Fin 3)) :
    fill a (stdSimplex.map (faceIndex i).succAbove x) = a i x := by
  change desc a (retract (face i x).val) = _
  rw [retract_fixed, desc_face]


private theorem skeleton_mem_horn (x : _root_.stdSimplex ℝ (Fin 4))
    (hx : x ∈ stdSimplex.skeleton 2 3) : ∃ i : Fin 3, x (faceIndex i) = 0 := by
  classical
  by_contra h
  push Not at h
  have hs : ({0, 2, 3} : Finset (Fin 4)) ⊆ (Finset.univ.filter fun j ↦ x j ≠ 0) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h 0⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h 1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h 2⟩
  have hc := Finset.card_le_card hs
  have hc3 : ({0, 2, 3} : Finset (Fin 4)).card = 3 := by decide
  rw [hc3] at hc
  change (Finset.univ.filter fun j ↦ x j ≠ 0).card ≤ 2 at hx
  omega

/-- Every original edge of the filled tetrahedron remains at the displayed basepoint. -/
theorem fill_skeleton (a : Fin 3 → SphericalSimplex Y y 2)
    (x : _root_.stdSimplex ℝ (Fin 4)) (hx : x ∈ stdSimplex.skeleton 2 3) : fill a x = y := by
  obtain ⟨i, hi⟩ := skeleton_mem_horn x hx
  have hm : x ∈ Set.range (stdSimplex.map (faceIndex i).succAbove) :=
    (stdSimplex.mem_range_map_succAbove_iff (faceIndex i) x).mpr hi
  obtain ⟨z, rfl⟩ := hm
  rw [fill_face]
  apply (a i).boundary
  apply stdSimplex.skeleton_subset_boundary (n := 2) (d := 2) le_rfl
  exact (stdSimplex.map_mem_skeleton_iff (faceIndex i).succAbove
    Fin.succAbove_right_injective z).mp hx

/-- The included spherical faces retain their literal original representatives. -/
theorem sphericalFace_fill (a : Fin 3 → SphericalSimplex Y y 2) (i : Fin 3) :
    sphericalFace (fill a) (fill_skeleton a) (faceIndex i) = a i := by
  ext x
  exact fill_face a i x

end Topology.SphericalHorn
