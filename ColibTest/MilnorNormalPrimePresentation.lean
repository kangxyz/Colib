/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Norm.NormalPrimePresentation

/-!
Consumers of the full normal-prime polynomial presentation.
They do not assert an identification with the chosen FieldNorm or its tower law.
-/

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K]

example [Algebra k K] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k e)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (hpsep : (poly p).Separable) (hqsep : (poly q).Separable)
    (hpsplit : ((poly p).map (algebraMap k K)).Splits)
    (hqsplit : ((poly q).map (algebraMap k K)).Splits)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKRingMap (algebraMap k K) (simpleMilnorNorm p x) =
      milnorKRingMap (algebraMap k K)
        (simpleMilnorNorm q (milnorKRingMap f.toRingHom x)) :=
  simpleMilnorNorm_map_eq_of_splits p q f hpsep hqsep hpsplit hqsplit x

example [PerfectField k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k e)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKRingMap (algebraMap k (k[X] ⧸ Ideal.span {poly p})) (simpleMilnorNorm p x) =
      milnorKRingMap (algebraMap k (k[X] ⧸ Ideal.span {poly p}))
        (simpleMilnorNorm q (milnorKRingMap f.toRingHom x)) :=
  simpleMilnorNorm_map_eq_over_normal p q f x

example [PerfectField k] {ell : ℕ} (p q : MonicIrreducibleOfDegree k ell)
    (hprime : ell.Prime) [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (m : ℕ) (x : MilnorKTheory (k[X] ⧸ Ideal.span {poly p}) (m + 1)) :
    simpleMilnorNorm p (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) =
      simpleMilnorNorm q (milnorKRingMap f.toRingHom
        (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) :=
  simpleMilnorNorm_eq_map_algEquiv_of_normal_prime_homogeneous p q hprime f m x

example [PerfectField k] {ell : ℕ} (p q : MonicIrreducibleOfDegree k ell)
    (hprime : ell.Prime) [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    simpleMilnorNorm p x = simpleMilnorNorm q (milnorKRingMap f.toRingHom x) :=
  simpleMilnorNorm_eq_map_algEquiv_of_normal_prime p q hprime f x

example [PerfectField k] {ell : ℕ} (p q : MonicIrreducibleOfDegree k ell)
    (hprime : ell.Prime) [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q})) :
    simpleMilnorNorm p =
      (simpleMilnorNorm q).comp (milnorKRingMap f.toRingHom).toAddMonoidHom :=
  simpleMilnorNorm_eq_comp_of_normal_prime p q hprime f

example [PerfectField k] {ell : ℕ} (p : MonicIrreducibleOfDegree k ell)
    (hprime : ell.Prime) [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p}))
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    simpleMilnorNorm p (milnorKRingMap f.toRingHom x) = simpleMilnorNorm p x :=
  (simpleMilnorNorm_eq_map_algEquiv_of_normal_prime p p hprime f x).symm

end
