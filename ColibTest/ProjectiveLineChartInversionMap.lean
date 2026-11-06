/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.ProjectiveLine.ChartInversionMap

/-! Uncompiled consumers of the existing chart inversion under coefficient extension. -/

noncomputable section

open Polynomial AlgebraicGeometry

universe u v

variable {k : Type u} [Field k] {K : Type v} [Field K]

example (φ : k →+* K) :
    (projectiveLineChartInversion K).toRingHom.comp
        (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) =
      (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)).comp
          (projectiveLineChartInversion k).toRingHom :=
  projectiveLineChartInversion_comp_mapRingHom φ

example (φ : k →+* K) (r : RatFunc k) :
    projectiveLineChartInversion K
        (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ) r) =
      RatFunc.mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
          (projectiveLineChartInversion k r) :=
  projectiveLineChartInversion_mapRingHom φ r

-- The statement applies to fractions, not only the polynomial image used in the ext proof.
example (φ : k →+* K) (a b : k[X]) :
    projectiveLineChartInversion K
        (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
          (algebraMap k[X] (RatFunc k) a / algebraMap k[X] (RatFunc k) b)) =
      RatFunc.mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
          (projectiveLineChartInversion k
            (algebraMap k[X] (RatFunc k) a / algebraMap k[X] (RatFunc k) b)) :=
  projectiveLineChartInversion_mapRingHom φ _

end
