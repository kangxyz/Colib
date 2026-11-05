/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Norm.UniformizerBinomial

/-! Actual DVR binomial consumers include inseparable characteristic, exponent
one, and the even/odd determinant signs. No integral basis is supplied.

Adapted from `AglibTest/DVRUniformizerBinomial.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`9d4eca59e745c56797e36dafa245bb60711845812519eccfa17482941d195e14`.
-/

noncomputable section

open Polynomial IsLocalRing

namespace ColibTest.DVRUniformizerBinomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]
  {c : R} (hc : Irreducible c)

include hc

/-- Every positive exponent gives fraction-field irreducibility. -/
theorem actual_irreducible (e : ℕ) (he : 0 < e) :
    Irreducible (X ^ e - C (algebraMap R F c)) :=
  IsDiscreteValuationRing.uniformizer_binomial_irreducible_fraction F hc e he

/-- A characteristic-p exponent is included; no separability assumption occurs.
The explicitly unused instance fixes this regression's characteristic. -/
theorem inseparable_exponent (p : ℕ) (hp : Nat.Prime p) [_characteristicP : CharP F p] :
    Irreducible (X ^ p - C (algebraMap R F c)) :=
  actual_irreducible F hc p hp.pos

variable {E : Type*} [Field E] [Algebra F E]

/-- The literal root equation fixes the actual minimal polynomial. -/
theorem actual_minpoly (e : ℕ) (he : 0 < e) (θ : E)
    (hθ : θ ^ e = algebraMap F E (algebraMap R F c)) :
    minpoly F θ = X ^ e - C (algebraMap R F c) :=
  IsDiscreteValuationRing.minpoly_eq_uniformizer_binomial F hc e he θ hθ

variable [FiniteDimensional F E]

/-- Actual equal dimensions imply generation of the whole field. -/
theorem actual_primitive (e : ℕ) (he : 0 < e) (hd : Module.finrank F E = e)
    (θ : E) (hθ : θ ^ e = algebraMap F E (algebraMap R F c)) :
    IntermediateField.adjoin F {θ} = ⊤ :=
  IsDiscreteValuationRing.adjoin_uniformizer_binomial_root_eq_top F hc e he hd θ hθ

/-- The smallest exponent is genuinely allowed. -/
theorem degree_one (hd : Module.finrank F E = 1) (θ : E)
    (hθ : θ = algebraMap F E (algebraMap R F c)) :
    Algebra.norm F θ = algebraMap R F c := by
  simpa only [Nat.sub_self, pow_zero, one_mul] using
    IsDiscreteValuationRing.norm_uniformizer_binomial_root F hc 1 (by decide) hd θ
      (by simpa only [pow_one] using hθ)

/-- The quadratic determinant has the negative sign, even when it becomes
trivial in characteristic two. -/
theorem quadratic_sign (hd : Module.finrank F E = 2) (θ : E)
    (hθ : θ ^ 2 = algebraMap F E (algebraMap R F c)) :
    Algebra.norm F θ = -algebraMap R F c := by
  simpa using IsDiscreteValuationRing.norm_uniformizer_binomial_root F hc 2 (by decide) hd θ hθ

/-- The cubic determinant has the positive sign. -/
theorem cubic_sign (hd : Module.finrank F E = 3) (θ : E)
    (hθ : θ ^ 3 = algebraMap F E (algebraMap R F c)) :
    Algebra.norm F θ = algebraMap R F c := by
  simpa using IsDiscreteValuationRing.norm_uniformizer_binomial_root F hc 3 (by decide) hd θ hθ

end ColibTest.DVRUniformizerBinomial
