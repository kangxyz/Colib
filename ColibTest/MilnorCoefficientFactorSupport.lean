/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.CoefficientFactorSupport

/-!
Source-only consumers of actual coefficient-factor support, with independent field universes.
These examples have not been elaborated or compiled.
-/

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u v

variable {k : Type u} [Field k] {K : Type v} [Field K]

example : Function.Injective
    (fun p : Σ d : ℕ, MonicIrreducibleOfDegree k d => poly p.2) :=
  sigma_poly_injective

example (φ : k →+* K) (f : k[X]) (hf : f ≠ 0) :
    ∃ S : Finset (Σ d : ℕ, MonicIrreducibleOfDegree K d),
      ∀ q, q ∈ S ↔ poly q.2 ∣ f.map φ :=
  exists_finset_mem_iff_dvd_map φ f hf

-- No positive-degree assumption is needed for the polynomial whose factors are collected.
example (φ : k →+* K) :
    ∃ S : Finset (Σ d : ℕ, MonicIrreducibleOfDegree K d),
      ∀ q, q ∈ S ↔ poly q.2 ∣ (1 : k[X]).map φ :=
  exists_finset_mem_iff_dvd_map φ 1 one_ne_zero

example [Algebra k K] [Algebra.IsAlgebraic k K]
    {e : ℕ} (q : MonicIrreducibleOfDegree K e) :
    ∃ d : ℕ, ∃ p : MonicIrreducibleOfDegree k d,
      poly q ∣ (poly p).map (algebraMap k K) :=
  exists_dvd_map_of_isIntegral q

example (φ : k →+* K) {e : ℕ} (q : MonicIrreducibleOfDegree K e)
    (a : k[X]) (ha : a ≠ 0) (hqa : poly q ∣ a.map φ) :
    ∃ d : ℕ, ∃ p : MonicIrreducibleOfDegree k d, poly q ∣ (poly p).map φ :=
  exists_dvd_map_of_dvd_map φ q a ha hqa

example (φ : k →+* K) {e : ℕ} (q : MonicIrreducibleOfDegree K e)
    (a : k[X]) (ha : a ≠ 0) (hqa : poly q ∣ a.map φ) :
    ∃ d : ℕ, ∃ p : MonicIrreducibleOfDegree k d,
      poly q ∣ (poly p).map φ ∧
        (Ideal.span ({poly q} : Set K[X])).comap (Polynomial.mapRingHom φ) =
          Ideal.span ({poly p} : Set k[X]) :=
  exists_comap_eq_of_dvd_map φ q a ha hqa

end
