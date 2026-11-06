/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.RatFunc.CoefficientMap
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineInfinity

/-!
# Coefficient extension and the existing projective-line chart inversion

The actual rational coefficient map commutes with the native chart change `X` to `1 / X`.
The proof uses its existing computations on constants and the coordinate, followed by
polynomial and localization extensionality. The field universes are independent.

No rational map or projective-line model is defined.
-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {K : Type v} [Field K]

/-- Native chart inversion commutes with the actual rational coefficient map. -/
theorem projectiveLineChartInversion_comp_mapRingHom (φ : k →+* K) :
    (projectiveLineChartInversion K).toRingHom.comp
        (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) =
      (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)).comp
          (projectiveLineChartInversion k).toRingHom := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  all_goals
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RatFunc.mapRingHom_algebraMap, Polynomial.coe_mapRingHom,
      Polynomial.map_C, Polynomial.map_X,
      projectiveLineChartInversion_C, projectiveLineChartInversion_X, map_inv₀]

/-- The same equality evaluated at an arbitrary rational function. -/
theorem projectiveLineChartInversion_mapRingHom (φ : k →+* K) (r : RatFunc k) :
    projectiveLineChartInversion K
        (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ) r) =
      RatFunc.mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
          (projectiveLineChartInversion k r) :=
  RingHom.congr_fun (projectiveLineChartInversion_comp_mapRingHom φ) r

end AlgebraicGeometry

end
