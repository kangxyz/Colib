/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Residue.CanonicalRamifiedMap

/-! Tests retain four independent universes and a genuine ramification unit. The degree-two
case tests the factor two, not vanishing in a residue field of characteristic two. -/

noncomputable section

universe u v w z

open Stacks.Chow

variable {R : Type u} {S : Type v}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {F : Type w} {E : Type z} [Field F] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
  (j : R →+* S) [IsLocalHom j] (f : F →+* E)
  (hf : ∀ r : R, f (algebraMap R F r) = algebraMap S E (j r))
  {π : R} {ρ : S} (hπ : Irreducible π) (hρ : Irreducible ρ)

example (u : Sˣ) (e : ℕ) (hπmap : j π = (u : S) * ρ ^ e)
    (n : ℕ) (x : MilnorKTheory F (n + 1)) :
    dvrMilnorTameSymbol' S E n (milnorKTheoryMap f (n + 1) x) =
      (e : ℤ) • milnorKTheoryMap (IsLocalRing.ResidueField.map j) n
        (dvrMilnorTameSymbol' R F n x) :=
  DFunLike.congr_fun (dvrMilnorTameSymbol'_map_ramified j f hf hπ hρ u e hπmap n) x

example (u : Sˣ) (hπmap : j π = (u : S) * ρ ^ 2) (x : MilnorKTheory F 2) :
    dvrMilnorTameSymbol' S E 1 (milnorKTheoryMap f 2 x) =
      (2 : ℤ) • milnorKTheoryMap (IsLocalRing.ResidueField.map j) 1
        (dvrMilnorTameSymbol' R F 1 x) :=
  DFunLike.congr_fun (dvrMilnorTameSymbol'_map_ramified j f hf hπ hρ u 2 hπmap 1) x

example {ρ : R} (hρ : Irreducible ρ) (n : ℕ) :
    dvrMilnorTameSymbol (F := F) hρ n = dvrMilnorTameSymbol (F := F) hπ n :=
  dvrMilnorTameSymbol_eq_of_ramified_identity hπ hρ n

example (n : ℕ) (x : MilnorKTheory F (n + 1)) :
    dvrMilnorTameSymbol' R F n x = dvrMilnorTameSymbol hπ n x :=
  DFunLike.congr_fun (dvrMilnorTameSymbol'_eq_of_ramified_identity hπ n) x
