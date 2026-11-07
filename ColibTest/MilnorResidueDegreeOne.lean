/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Residue.DegreeOne

/-! Native degree-one residue regression tests with explicit universe and map hypotheses. -/

open Stacks.Chow

universe u v

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]

-- The whole native K1, not just a chosen symbol, is compared with the integer order.
example {π : R} (hπ : Irreducible π) (x : MilnorKTheory F 1) :
    milnorKTheoryZeroAddEquiv (IsLocalRing.ResidueField R) (dvrMilnorTameSymbol hπ 0 x) =
      dvrFracOrd hπ (milnorKTheoryOneAddEquiv F x).toMul :=
  milnorKTheoryZeroAddEquiv_dvrMilnorTameSymbol hπ x

-- Kernel membership yields an actual unit of the DVR, in independent universes.
example (x : MilnorKTheory F 1) (hx : dvrMilnorTameSymbol' R F 0 x = 0) :
    ∃ a : Rˣ, (milnorKTheoryOneAddEquiv F x).toMul =
      Units.map (algebraMap R F).toMonoidHom a :=
  (dvrMilnorTameSymbol'_one_eq_zero_iff x).mp hx

example {π : R} (hπ : Irreducible π) (x : MilnorKTheory F 1) :
    dvrMilnorTameSymbol hπ 0 x = 0 ↔
      ∃ a : Rˣ, (milnorKTheoryOneAddEquiv F x).toMul =
        Units.map (algebraMap R F).toMonoidHom a :=
  dvrMilnorTameSymbol_one_eq_zero_iff hπ x

example (x : MilnorKTheory F 1) (a : Rˣ)
    (ha : (milnorKTheoryOneAddEquiv F x).toMul =
      Units.map (algebraMap R F).toMonoidHom a) :
    dvrMilnorTameSymbol' R F 0 x = 0 :=
  (dvrMilnorTameSymbol'_one_eq_zero_iff x).mpr ⟨a, ha⟩
