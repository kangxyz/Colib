/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.Util.References
public import Colib.Analysis.Convex.StdSimplex.BarycentricSubdivision
public import Mathlib.Topology.Homotopy.Path

/-! # Coordinate interpolation of native simplex paths

Adapted from `Quillen/Topology/Realization/SimplexHomotopy.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, directly on the pinned native
standard simplex. The actual interpolation parameter and both endpoints are
retained, so later cap normalization can inspect its coordinates.
-/
@[expose] public noncomputable section
open scoped Topology unitInterval
namespace stdSimplex

/-- Interpolate two paths by their original real coordinates, fixing both endpoints. -/
def pathHomotopy {M : Type*} [Fintype M]
    {x y : _root_.stdSimplex ℝ M} (p q : Path x y) : p.Homotopy q where
  toFun z := ⟨fun i ↦ (1 - (z.1 : ℝ)) * p z.2 i + (z.1 : ℝ) * q z.2 i,
    fun i ↦ add_nonneg
      (mul_nonneg (sub_nonneg.mpr z.1.property.2) (stdSimplex.zero_le _ _))
      (mul_nonneg z.1.property.1 (stdSimplex.zero_le _ _)), by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        stdSimplex.sum_eq_one, stdSimplex.sum_eq_one]
      ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    have hp : Continuous (fun z : unitInterval × unitInterval ↦ p z.2 i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp
        (p.continuous.comp continuous_snd))
    have hq : Continuous (fun z : unitInterval × unitInterval ↦ q z.2 i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp
        (q.continuous.comp continuous_snd))
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hp).add
      ((continuous_subtype_val.comp continuous_fst).mul hq)
  map_zero_left t := by
    ext i
    change (1 - (0 : ℝ)) * p t i + (0 : ℝ) * q t i = p t i
    simp
  map_one_left t := by
    ext i
    change (1 - (1 : ℝ)) * p t i + (1 : ℝ) * q t i = q t i
    simp
  prop' t z hz := by
    rcases hz with hz | hz
    · subst z
      ext i
      change (1 - (t : ℝ)) * p 0 i + (t : ℝ) * q 0 i = p 0 i
      simp only [Path.source]
      ring
    · rw [Set.mem_singleton_iff] at hz
      subst z
      ext i
      change (1 - (t : ℝ)) * p 1 i + (t : ℝ) * q 1 i = p 1 i
      simp only [Path.target]
      ring

/-- The interpolating homotopy retains its exact two affine weights. -/
@[simp]
theorem pathHomotopy_apply {M : Type*} [Fintype M]
    {x y : _root_.stdSimplex ℝ M} (p q : Path x y)
    (t s : unitInterval) (i : M) :
    pathHomotopy p q (t, s) i = (1 - (t : ℝ)) * p s i + (t : ℝ) * q s i := rfl

/-- Native fixed-endpoint interpolation exhibits the homotopy class equality. -/
theorem paths_homotopic {M : Type*} [Fintype M]
    {x y : _root_.stdSimplex ℝ M} (p q : Path x y) : p.Homotopic q :=
  ⟨pathHomotopy p q⟩

end stdSimplex

attribute [colib_tag "COL-0082",
  colib_ref "HatcherAT" "Section 1.1, Example 1.1, page 25"
    "adaptation"
    "Endpoint-fixed linear interpolation in finite real barycentric simplices"]
  stdSimplex.pathHomotopy
  stdSimplex.paths_homotopic
