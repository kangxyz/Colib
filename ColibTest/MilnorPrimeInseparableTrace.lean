/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeInseparableTrace

/-!
Regression consumers of restriction of the actual chosen norm in purely
inseparable prime degree. No perfectness, characteristic-zero, normality, or
separability instance is assumed. No Lean/Lake command has been run on this file.
-/

noncomputable section

open Module Stacks.Chow

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

example [FiniteDimensional K L] [IsPurelyInseparable K L]
    (hp : Nat.Prime (finrank K L)) (x : MilnorKRing L) :
    milnorKRingMap (algebraMap K L) (milnorKNormRing K L x) =
      (finrank K L : ℤ) • x :=
  milnorKRingMap_milnorKNormRing_of_isPurelyInseparable_of_prime hp x

example [FiniteDimensional K L] [IsPurelyInseparable K L]
    (hp : Nat.Prime (finrank K L)) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTheoryMap (algebraMap K L) n (milnorKNorm K L n x) =
      (finrank K L : ℤ) • x :=
  milnorKTheoryMap_milnorKNorm_of_isPurelyInseparable_of_prime hp n x

example [FiniteDimensional K L] [IsPurelyInseparable K L]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hdegree : finrank K L = ℓ)
    (x : MilnorKTheory L 0) :
    milnorKTheoryMap (algebraMap K L) 0 (milnorKNorm K L 0 x) = (ℓ : ℤ) • x := by
  have hp : Nat.Prime (finrank K L) := hdegree.symm ▸ hℓ
  simpa only [hdegree] using
    milnorKTheoryMap_milnorKNorm_of_isPurelyInseparable_of_prime hp 0 x

end
