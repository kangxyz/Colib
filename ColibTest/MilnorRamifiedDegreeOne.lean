/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Residue.RamifiedDegreeOne

/-! Native degree-one residue regression tests with explicit universe and map hypotheses. -/

open Stacks.Chow

universe u v w z

variable {R : Type u} {S : Type v}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {F : Type w} {E : Type z} [Field F] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
  (j : R →+* S) (f : F →+* E)
  (hf : ∀ r : R, f (algebraMap R F r) = algebraMap S E (j r))
  {π : R} {ρ : S} (hπ : Irreducible π) (hρ : Irreducible ρ)

-- All four universes and an arbitrary native K1 class.
example (u : Sˣ) (e : ℕ) (hπmap : j π = (u : S) * ρ ^ e) (x : MilnorKTheory F 1) :
    milnorKTheoryZeroAddEquiv (IsLocalRing.ResidueField S)
        (dvrMilnorTameSymbol hρ 0 (milnorKTheoryMap f 1 x)) =
      (e : ℤ) * milnorKTheoryZeroAddEquiv (IsLocalRing.ResidueField R)
        (dvrMilnorTameSymbol hπ 0 x) :=
  dvrMilnorTameSymbol_one_map_ramified j f hf hπ hρ u e hπmap x

-- Without a local-map assumption, exponent zero is allowed by the exact algebraic statement.
example (u : Sˣ) (hπmap : j π = (u : S) * ρ ^ 0) (x : MilnorKTheory F 1) :
    milnorKTheoryZeroAddEquiv (IsLocalRing.ResidueField S)
        (dvrMilnorTameSymbol hρ 0 (milnorKTheoryMap f 1 x)) = 0 := by
  simpa using dvrMilnorTameSymbol_one_map_ramified j f hf hπ hρ u 0 hπmap x

-- A genuinely local map rules out exponent zero directly from the uniformizer equation.
example [IsLocalHom j] (u : Sˣ) (e : ℕ) (hπmap : j π = (u : S) * ρ ^ e) : 0 < e := by
  apply Nat.pos_of_ne_zero
  intro he
  have hu : IsUnit (j π) := by
    rw [hπmap, he, pow_zero, mul_one]
    exact u.isUnit
  exact hπ.not_isUnit (isUnit_of_map_unit j π hu)
