/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Norm.NormalPrimeChosenComparison

/-!
UNCOMPILED consumers of the native normal-prime chosen-norm comparison.
These examples use actual polynomial presentations and algebra equivalences.
No norm-invariance premise or norm tower law is supplied.
-/

noncomputable section

open Polynomial Module Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field

variable {k L M : Type u} [Field k] [Field L] [Field M]

section Presentation

variable [Algebra k L] [FiniteDimensional k L] [PerfectField k] [Normal k L]

example (hp : Nat.Prime (finrank k L)) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d)
    (f : L ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p})) (x : MilnorKRing L) :
    milnorKNormRing k L x = simpleMilnorNorm p (milnorKRingMap f.toRingHom x) :=
  milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime hp p f x

example (hp : Nat.Prime (finrank k L)) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d)
    (f : L ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p})) :
    milnorKNormRing k L =
      (simpleMilnorNorm p).comp (milnorKRingMap f.toRingHom).toAddMonoidHom :=
  milnorKNormRing_eq_comp_simpleMilnorNorm_of_algEquiv_of_normal_prime hp p f

end Presentation

example [PerfectField k] {d : ℕ} (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    letI : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
      (AdjoinRoot.powerBasis' (monic p)).finite
    milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x = simpleMilnorNorm p x := by
  let : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
    (AdjoinRoot.powerBasis' (monic p)).finite
  exact milnorKNormRing_eq_simpleMilnorNorm_of_normal_prime p hp x

section Equivariance

variable [Algebra k L] [Algebra k M] [FiniteDimensional k L] [FiniteDimensional k M]
  [PerfectField k] [Normal k L]

example (hp : Nat.Prime (finrank k L)) (f : L ≃ₐ[k] M) (x : MilnorKRing L) :
    milnorKNormRing k M (milnorKRingMap f.toRingHom x) = milnorKNormRing k L x :=
  milnorKNormRing_map_algEquiv_of_normal_prime hp f x

example (hp : Nat.Prime (finrank k L)) (f : L ≃ₐ[k] M) :
    (milnorKNormRing k M).comp (milnorKRingMap f.toRingHom).toAddMonoidHom =
      milnorKNormRing k L :=
  milnorKNormRing_comp_map_algEquiv_of_normal_prime hp f

example (hp : Nat.Prime (finrank k L)) (f : L ≃ₐ[k] M)
    (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNorm k M n (milnorKTheoryMap f.toRingHom n x) = milnorKNorm k L n x :=
  milnorKNorm_map_algEquiv_of_normal_prime hp f n x

end Equivariance

example [Algebra k L] [FiniteDimensional k L] [PerfectField k] [Normal k L]
    (hp : Nat.Prime (finrank k L)) (f : L ≃ₐ[k] L) (x : MilnorKRing L) :
    milnorKNormRing k L (milnorKRingMap f.toRingHom x) = milnorKNormRing k L x :=
  milnorKNormRing_map_algEquiv_of_normal_prime hp f x

end
