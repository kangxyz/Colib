/-
Copyright (c) 2025 Joël Riou and 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-!
# Degree-zero cocycles in a native projective resolution

There are no coboundaries in degree zero of the Hom complex of a projective
resolution. The cocycle reduction is adapted from Joël Riou's proof of
`ProjectiveResolution.extMk_eq_zero_iff` in the pinned Mathlib
`CategoryTheory.Abelian.Projective.Ext`; the degree-zero vanishing argument
is supplied here. This complements the positive-degree `extMk_eq_zero_iff` API
and supplies the empty-sequence case of the native Koszul coefficient formula.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex

universe w

namespace CategoryTheory.ProjectiveResolution

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]
  {X Y : C} (P : ProjectiveResolution X)

/-- A degree-zero resolution cocycle represents zero exactly when the cocycle is zero. -/
theorem extMk_zero_eq_zero_iff (f : P.complex.X 0 ⟶ Y)
    (hf : P.complex.d 1 0 ≫ f = 0) : P.extMk f 1 rfl hf = 0 ↔ f = 0 := by
  simp only [← P.extEquivCohomologyClass.apply_eq_iff_eq,
    extEquivCohomologyClass_extMk, extEquivCohomologyClass_zero,
    CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ 1 (by simp)]
  constructor
  · rintro ⟨g, hg⟩
    have hg0 : g = 0 := (P.cochainComplex.isZero_of_isStrictlyLE 0 1).eq_of_src _ _
    rw [hg0, comp_zero] at hg
    exact (cancel_epi (P.cochainComplexXIso 0 0).hom).mp (by simpa using hg.symm)
  · intro hf0
    subst f
    exact ⟨0, by simp⟩

end CategoryTheory.ProjectiveResolution
