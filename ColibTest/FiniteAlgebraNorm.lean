/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.LinearAlgebra.Determinant.FiniteLength
import Colib.RingTheory.Norm.FiniteAlgebra
import Colib.RingTheory.Norm.PolynomialFiber
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.LocalRing.NonLocalRing

/-!
# Regressions for finite-algebra norms and polynomial evaluation fibres

The base field, finite algebra and module have independent universes. The module
regressions are not restricted to the regular module of the algebra. Products use
all maximal ideals, and the finite local lengths are checked before their `toNat`
values become exponents. The concrete algebra `DualNumber k × k` is both nonlocal
and nonreduced; its square-zero witness is displayed explicitly.

The polynomial tests retain the literal evaluation tensor products, native pure
tensors, quotient fields and localizations. No replacement fibre, residue field,
localization, or specialization model is introduced. Finite torsion-freeness is
tested separately from a supplied free-module instance.

-/

noncomputable section

open scoped BigOperators TensorProduct
open Polynomial

attribute [local instance] Ideal.Quotient.field

universe u v w

section FiniteLengthDeterminant

variable (k : Type u) (M : Type w) [Field k] [AddCommGroup M]
  [Module k M] [Module.Finite k M]

-- The native finite-length determinant and ordinary determinant use the same endomorphism.
example (hM : IsFiniteLength k M) (f : Module.End k M) :
    FiniteLengthEndomorphism.det k hM f = IsLocalRing.residue k f.det :=
  FiniteLengthEndomorphism.det_eq_residue_det (k := k) hM f

end FiniteLengthDeterminant

section FiniteAlgebra

variable (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B]
  [Module.Finite k B]

-- Finiteness is established in ℕ∞ before using a natural-number multiplicity.
example (q : MaximalSpectrum B) :
    Module.length (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal) ≠ ⊤ :=
  Algebra.local_length_ne_top_of_finite (k := k) q

example [Fintype (MaximalSpectrum B)] (b : B) :
    Algebra.norm k b = ∏ q : MaximalSpectrum B,
      Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
        (Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat :=
  Algebra.norm_eq_prod_quotient_norm_pow_local_length (k := k) b

-- The intrinsic product needs no caller-provided enumeration or reducedness hypothesis.
example (b : B) :
    Algebra.norm k b = ∏ᶠ q : MaximalSpectrum B,
      Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
        (Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat :=
  Algebra.norm_eq_finprod_quotient_norm_pow_local_length (k := k) b

-- Every element, rather than just a unit, is covered by the finite-algebra formula.
example :
    Algebra.norm k (0 : B) = ∏ᶠ q : MaximalSpectrum B,
      Algebra.norm k (Ideal.Quotient.mk q.asIdeal (0 : B)) ^
        (Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat :=
  Algebra.norm_eq_finprod_quotient_norm_pow_local_length (k := k) (0 : B)

-- The zero algebra has determinant norm one, even at zero.
example [Subsingleton B] (b : B) : Algebra.norm k b = 1 := by
  rw [Algebra.norm_apply]
  exact LinearMap.det_eq_one_of_subsingleton _

example [Subsingleton B] (b : B) :
    (∏ᶠ q : MaximalSpectrum B,
      Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
        (Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat) = 1 := by
  rw [← Algebra.norm_eq_finprod_quotient_norm_pow_local_length (k := k) b,
    Algebra.norm_apply]
  exact LinearMap.det_eq_one_of_subsingleton _

end FiniteAlgebra

section LocalSelfLength

variable (B : Type v) [CommRing B] [IsLocalRing B]

-- This structural identity does not require a field base or finiteness.
example :
    Module.length (Localization.AtPrime (IsLocalRing.maximalIdeal B))
      (Localization.AtPrime (IsLocalRing.maximalIdeal B)) = Module.length B B :=
  IsLocalRing.length_localization_maximalIdeal B

end LocalSelfLength

section LocalAlgebra

variable (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B]
  [Module.Finite k B] [IsLocalRing B]

-- The local case uses the full self-length, including nilpotent multiplicity.
example (b : B) :
    Algebra.norm k b =
      Algebra.norm k (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) b) ^
        (Module.length B B).toNat :=
  Algebra.norm_eq_quotient_norm_pow_length (k := k) b

end LocalAlgebra

section FieldExtension

variable (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
  [Module.Finite k E]

-- Inseparable extensions are not excluded by an extra separability assumption.
example (x : E) :
    Algebra.norm k x = ∏ᶠ q : MaximalSpectrum E,
      Algebra.norm k (Ideal.Quotient.mk q.asIdeal x) ^
        (Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat :=
  Algebra.norm_eq_finprod_quotient_norm_pow_local_length (k := k) x

end FieldExtension

section ArbitraryModules

variable (k : Type u) (B : Type v) (M : Type w)
  [Field k] [CommRing B] [Algebra k B] [Module.Finite k B]
  [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]
  [Module.Finite k M]

-- Both native and tensor local modules have finite length before any use of toNat.
example (q : MaximalSpectrum B) :
    Module.length (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal ⊗[B] M) ≠ ⊤ :=
  Module.localized_length_ne_top_of_finiteDimensional (k := k) (M := M) q

example (q : MaximalSpectrum B) :
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M) ≠ ⊤ := by
  rw [(LocalizedModule.equivTensorProduct q.asIdeal.primeCompl M).length_eq]
  exact Module.localized_length_ne_top_of_finiteDimensional (k := k) (M := M) q

-- This tests scalar multiplication on an arbitrary compatible finite module.
example [Fintype (MaximalSpectrum B)] (b : B) :
    LinearMap.det ((LinearMap.lsmul B M b).restrictScalars k) =
      ∏ q : MaximalSpectrum B,
        Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
          (Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat :=
  Module.det_lsmul_eq_prod_norm_pow_localized_length (k := k) (M := M) b

example [Fintype (MaximalSpectrum B)] (b : B) :
    LinearMap.det ((LinearMap.lsmul B M b).restrictScalars k) =
      ∏ q : MaximalSpectrum B,
        Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
          (Module.length (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime q.asIdeal ⊗[B] M)).toNat :=
  Module.det_lsmul_eq_prod_norm_pow_localized_length_tensor (k := k) (M := M) b

example (b : B) :
    LinearMap.det ((LinearMap.lsmul B M b).restrictScalars k) =
      ∏ᶠ q : MaximalSpectrum B,
        Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
          (Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat :=
  Module.det_lsmul_eq_finprod_norm_pow_localized_length (k := k) (M := M) b

example (b : B) :
    LinearMap.det ((LinearMap.lsmul B M b).restrictScalars k) =
      ∏ᶠ q : MaximalSpectrum B,
        Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
          (Module.length (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime q.asIdeal ⊗[B] M)).toNat :=
  Module.det_lsmul_eq_finprod_norm_pow_localized_length_tensor (k := k) (M := M) b

-- A zero module has determinant one and contributes only zero multiplicities.
example [Subsingleton M] (b : B) :
    (∏ᶠ q : MaximalSpectrum B,
      Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
        (Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M)).toNat) = 1 := by
  rw [← Module.det_lsmul_eq_finprod_norm_pow_localized_length (k := k) (M := M) b]
  exact LinearMap.det_eq_one_of_subsingleton _

end ArbitraryModules

section NonlocalNonreduced

variable (k : Type u) [Field k]

local instance : Module.Finite k (DualNumber k) := by
  change Module.Finite k (k × k)
  infer_instance

example : Module.Finite k (DualNumber k × k) := inferInstance

example : ¬ IsLocalRing (DualNumber k × k) :=
  IsLocalRing.not_isLocalRing_of_prod_of_nontrivial (DualNumber k) k

-- This actual finite algebra contains a nonzero square-zero element.
example : ∃ e : DualNumber k × k, e ≠ 0 ∧ e ^ 2 = 0 := by
  refine ⟨(DualNumber.eps, 0), ?_, ?_⟩
  · intro h
    have h' : (1 : k) = 0 := by
      simpa using congrArg (fun x : DualNumber k × k => TrivSqZeroExt.snd x.1) h
    exact one_ne_zero h'
  · ext <;> simp

example (b : DualNumber k × k) :
    Algebra.norm k b = ∏ᶠ q : MaximalSpectrum (DualNumber k × k),
      Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
        (Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat :=
  Algebra.norm_eq_finprod_quotient_norm_pow_local_length (k := k) b

variable (M : Type w) [AddCommGroup M] [Module (DualNumber k × k) M]
  [Module k M] [IsScalarTower k (DualNumber k × k) M] [Module.Finite k M]

-- Nonlocal and nonreduced coverage also uses an arbitrary module, not only the ring.
example (b : DualNumber k × k) :
    LinearMap.det ((LinearMap.lsmul (DualNumber k × k) M b).restrictScalars k) =
      ∏ᶠ q : MaximalSpectrum (DualNumber k × k),
        Algebra.norm k (Ideal.Quotient.mk q.asIdeal b) ^
          (Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat :=
  Module.det_lsmul_eq_finprod_norm_pow_localized_length (k := k) (M := M) b

end NonlocalNonreduced

section ProductValue

variable (k : Type u) [Field k]

-- This checks the numerical value: both disconnected branches contribute.
example (a b : k) :
    a * b = ∏ᶠ q : MaximalSpectrum (k × k),
      Algebra.norm k (Ideal.Quotient.mk q.asIdeal (a, b)) ^
        (Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat := by
  rw [← Algebra.norm_eq_finprod_quotient_norm_pow_local_length (k := k) (a, b),
    Algebra.norm_apply]
  have h : Algebra.lmul k (k × k) (a, b) =
      (LinearMap.mulLeft k a).prodMap (LinearMap.mulLeft k b) := by
    apply LinearMap.ext
    intro x
    rfl
  rw [h, LinearMap.det_prodMap, LinearMap.det_mulLeft, LinearMap.det_mulLeft]

end ProductValue

section PolynomialEvaluation

variable (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k[X] B]

-- A global unit has constant polynomial norm, without a freeness assumption here.
example (u : Bˣ) :
    ∃ c : kˣ, Algebra.norm k[X] (u : B) = Polynomial.C (c : k) :=
  Algebra.PolynomialFiber.norm_unit_eq_C (k := k) u

-- Single-fibre factorization only needs finiteness, not flatness or torsion-freeness.
example [Module.Finite k[X] B] (a : k) (x : B) :
    letI := (Polynomial.evalRingHom a).toAlgebra
    Algebra.norm k (1 ⊗ₜ[k[X]] x : k ⊗[k[X]] B) =
      ∏ᶠ q : MaximalSpectrum (k ⊗[k[X]] B),
        Algebra.norm k (Ideal.Quotient.mk q.asIdeal (1 ⊗ₜ[k[X]] x)) ^
          (Module.length (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime q.asIdeal)).toNat :=
  Algebra.PolynomialFiber.norm_one_tmul_eq_finprod a x

example [Module.Free k[X] B] [Module.Finite k[X] B] (a : k) (x : B) :
    (letI := (Polynomial.evalRingHom a).toAlgebra
     Algebra.norm k (1 ⊗ₜ[k[X]] x : k ⊗[k[X]] B)) =
      (Algebra.norm k[X] x).eval a :=
  Algebra.PolynomialFiber.norm_one_tmul a x

-- Distinct evaluation actions are kept on the two literal tensor-product expressions.
example [Module.Free k[X] B] [Module.Finite k[X] B] (u : Bˣ) (a b : k) :
    (letI := (Polynomial.evalRingHom a).toAlgebra
     Algebra.norm k (1 ⊗ₜ[k[X]] (u : B) : k ⊗[k[X]] B)) =
    (letI := (Polynomial.evalRingHom b).toAlgebra
     Algebra.norm k (1 ⊗ₜ[k[X]] (u : B) : k ⊗[k[X]] B)) :=
  Algebra.PolynomialFiber.norm_one_tmul_eq u a b

example [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B] (u : Bˣ) (a b : k) :
    (letI := (Polynomial.evalRingHom a).toAlgebra
     Algebra.norm k (1 ⊗ₜ[k[X]] (u : B) : k ⊗[k[X]] B)) =
    (letI := (Polynomial.evalRingHom b).toAlgebra
     Algebra.norm k (1 ⊗ₜ[k[X]] (u : B) : k ⊗[k[X]] B)) :=
  Algebra.PolynomialFiber.norm_one_tmul_eq_of_torsionFree u a b

-- Equality is also retained in the native unit group kˣ.
example [Module.Free k[X] B] [Module.Finite k[X] B] (u : Bˣ) (a b : k) :
    (letI := (Polynomial.evalRingHom a).toAlgebra
     Units.map (Algebra.norm k)
       (Units.map (Algebra.TensorProduct.includeRight :
         B →ₐ[k[X]] k ⊗[k[X]] B).toMonoidHom u)) =
    (letI := (Polynomial.evalRingHom b).toAlgebra
     Units.map (Algebra.norm k)
       (Units.map (Algebra.TensorProduct.includeRight :
         B →ₐ[k[X]] k ⊗[k[X]] B).toMonoidHom u)) :=
  Algebra.PolynomialFiber.normUnits_one_tmul_eq u a b

example [Module.Free k[X] B] [Module.Finite k[X] B] (u : Bˣ) (a b : k) :
    (letI := (Polynomial.evalRingHom a).toAlgebra
     ∏ᶠ q : MaximalSpectrum (k ⊗[k[X]] B),
       Algebra.norm k (Ideal.Quotient.mk q.asIdeal (1 ⊗ₜ[k[X]] (u : B))) ^
         (Module.length (Localization.AtPrime q.asIdeal)
           (Localization.AtPrime q.asIdeal)).toNat) =
    (letI := (Polynomial.evalRingHom b).toAlgebra
     ∏ᶠ q : MaximalSpectrum (k ⊗[k[X]] B),
       Algebra.norm k (Ideal.Quotient.mk q.asIdeal (1 ⊗ₜ[k[X]] (u : B))) ^
         (Module.length (Localization.AtPrime q.asIdeal)
           (Localization.AtPrime q.asIdeal)).toNat) :=
  Algebra.PolynomialFiber.finprod_residue_norm_eq u a b

example [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B] (u : Bˣ) (a b : k) :
    (letI := (Polynomial.evalRingHom a).toAlgebra
     ∏ᶠ q : MaximalSpectrum (k ⊗[k[X]] B),
       Algebra.norm k (Ideal.Quotient.mk q.asIdeal (1 ⊗ₜ[k[X]] (u : B))) ^
         (Module.length (Localization.AtPrime q.asIdeal)
           (Localization.AtPrime q.asIdeal)).toNat) =
    (letI := (Polynomial.evalRingHom b).toAlgebra
     ∏ᶠ q : MaximalSpectrum (k ⊗[k[X]] B),
       Algebra.norm k (Ideal.Quotient.mk q.asIdeal (1 ⊗ₜ[k[X]] (u : B))) ^
         (Module.length (Localization.AtPrime q.asIdeal)
           (Localization.AtPrime q.asIdeal)).toNat) :=
  Algebra.PolynomialFiber.finprod_residue_norm_eq_of_torsionFree u a b

end PolynomialEvaluation
