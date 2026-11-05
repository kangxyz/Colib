/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Residue.RightBaseFieldProduct

open Stacks.Chow

universe u v w

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]
  {k : Type w} [Field k]

-- Both factors are arbitrary classes, with three independent universes.
example (f : k →+* R) (n m : ℕ)
    (z : MilnorKTheory F (n + 1)) (x : MilnorKTheory k m) :
    dvrMilnorTameSymbol' R F (n + m)
      (cast (congrArg (MilnorKTheory F) (Nat.add_right_comm n 1 m))
        (GradedMonoid.GMul.mul (i := n + 1) (j := m) z
          (milnorKTheoryMap ((algebraMap R F).comp f) m x))) =
      (-1 : ℤ) ^ m • GradedMonoid.GMul.mul (i := n) (j := m)
        (dvrMilnorTameSymbol' R F n z)
        (milnorKTheoryMap ((IsLocalRing.residue R).comp f) m x) :=
  dvrMilnorTameSymbol'_mul_baseField f n m z x

-- Right degree one gives additive negation, without any nonvanishing assertion.
example (f : k →+* R) (n : ℕ)
    (z : MilnorKTheory F (n + 1)) (x : MilnorKTheory k 1) :
    dvrMilnorTameSymbol' R F (n + 1)
      (GradedMonoid.GMul.mul (i := n + 1) (j := 1) z
        (milnorKTheoryMap ((algebraMap R F).comp f) 1 x)) =
      -GradedMonoid.GMul.mul (i := n) (j := 1)
        (dvrMilnorTameSymbol' R F n z)
        (milnorKTheoryMap ((IsLocalRing.residue R).comp f) 1 x) := by
  simpa using dvrMilnorTameSymbol'_mul_baseField f n 1 z x
