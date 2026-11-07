/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Residue.BaseFieldProduct

universe u v w

open Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]
  {k : Type w} [Field k]

-- All three universes are independent; both factors are arbitrary homogeneous classes.
example (f : k →+* R) (m n : ℕ) (x : MilnorKTheory k m) (z : MilnorKTheory F (n + 1)) :
    dvrMilnorTameSymbol' R F (m + n)
      (GradedMonoid.GMul.mul (i := m) (j := n + 1)
        (milnorKTheoryMap ((algebraMap R F).comp f) m x) z) =
      GradedMonoid.GMul.mul (i := m) (j := n)
        (milnorKTheoryMap ((IsLocalRing.residue R).comp f) m x)
        (dvrMilnorTameSymbol' R F n z) :=
  dvrMilnorTameSymbol'_baseField_mul f m n x z

-- Degree-zero action and degree-zero residue target need no exceptional hypotheses.
example (f : k →+* R) (x : MilnorKTheory k 0) (z : MilnorKTheory F 1) :
    dvrMilnorTameSymbol' R F 0
      (GradedMonoid.GMul.mul (i := 0) (j := 1)
        (milnorKTheoryMap ((algebraMap R F).comp f) 0 x) z) =
      GradedMonoid.GMul.mul (i := 0) (j := 0)
        (milnorKTheoryMap ((IsLocalRing.residue R).comp f) 0 x)
        (dvrMilnorTameSymbol' R F 0 z) :=
  dvrMilnorTameSymbol'_baseField_mul f 0 0 x z
