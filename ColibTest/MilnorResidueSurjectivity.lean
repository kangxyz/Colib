/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Residue.Surjectivity

open Stacks.Chow

universe u v

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]

-- Arbitrary target classes and independent ring/fraction-field universes.
example (n : ℕ) (y : MilnorKTheory (IsLocalRing.ResidueField R) n) :
    ∃ x : MilnorKTheory F (n + 1), dvrMilnorTameSymbol' R F n x = y :=
  dvrMilnorTameSymbol'_surjective n y

-- The target degree-zero group is included, without a positivity hypothesis.
example (y : MilnorKTheory (IsLocalRing.ResidueField R) 0) :
    ∃ x : MilnorKTheory F 1, dvrMilnorTameSymbol' R F 0 x = y :=
  dvrMilnorTameSymbol'_surjective 0 y

-- No special property of the canonical uniformizer is needed.
example {π : R} (hπ : Irreducible π) (n : ℕ)
    (y : MilnorKTheory (IsLocalRing.ResidueField R) n) :
    ∃ x : MilnorKTheory F (n + 1), dvrMilnorTameSymbol hπ n x = y :=
  dvrMilnorTameSymbol_surjective hπ n y
