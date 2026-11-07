/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Residue.SpecializationProduct

universe u v

open Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F] {π : R}

-- Arbitrary classes and independent universes; neither factor is restricted to a symbol.
example (hπ : Irreducible π) (m n : ℕ)
    (x : MilnorKTheory F m) (y : MilnorKTheory F n) :
    dvrMilnorSpecialization hπ (m + n) (GradedMonoid.GMul.mul (i := m) (j := n) x y) =
      GradedMonoid.GMul.mul (i := m) (j := n)
        (dvrMilnorSpecialization hπ m x) (dvrMilnorSpecialization hπ n y) :=
  dvrMilnorSpecialization_gmul hπ m n x y

-- Both factors may have degree zero.
example (hπ : Irreducible π) (x y : MilnorKTheory F 0) :
    dvrMilnorSpecialization hπ 0 (GradedMonoid.GMul.mul (i := 0) (j := 0) x y) =
      GradedMonoid.GMul.mul (i := 0) (j := 0)
        (dvrMilnorSpecialization hπ 0 x) (dvrMilnorSpecialization hπ 0 y) :=
  dvrMilnorSpecialization_gmul hπ 0 0 x y
