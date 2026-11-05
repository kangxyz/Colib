/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Residue.RamifiedSpecialization
import Colib.KTheory.MilnorK.Residue.CanonicalNormalization

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
    dvrMilnorSpecialization hρ (n + 1) (milnorKTheoryMap f (n + 1) x) =
      milnorKTheoryMap (IsLocalRing.ResidueField.map j) (n + 1)
          (dvrMilnorSpecialization hπ (n + 1) x) +
        GradedMonoid.GMul.mul (i := n) (j := 1)
          (milnorKTheoryMap (IsLocalRing.ResidueField.map j) n (dvrMilnorTameSymbol' R F n x))
          (milnorKTupleSymbol
            (fun _ : Fin 1 => Units.map (IsLocalRing.residue S).toMonoidHom u)) :=
  dvrMilnorSpecialization_map_ramified j f hf hπ hρ u e hπmap n x

example :
    dvrMilnorTameSymbol' R F 0
      (milnorKTupleSymbol (Fin.snoc (Fin.elim0 : Fin 0 → Fˣ) (dvrFracUniformizer F hπ))) =
        milnorKTupleSymbol (Fin.elim0 : Fin 0 → (IsLocalRing.ResidueField R)ˣ) := by
  have hf0 : Units.map (algebraMap R F).toMonoidHom ∘ (Fin.elim0 : Fin 0 → Rˣ) =
      (Fin.elim0 : Fin 0 → Fˣ) := funext fun i => Fin.elim0 i
  have hr0 : Units.map (IsLocalRing.residue R).toMonoidHom ∘ (Fin.elim0 : Fin 0 → Rˣ) =
      (Fin.elim0 : Fin 0 → (IsLocalRing.ResidueField R)ˣ) := funext fun i => Fin.elim0 i
  simpa only [hf0, hr0] using
    dvrMilnorTameSymbol'_tuple_snoc_uniformizer (F := F) hπ 0 (Fin.elim0 : Fin 0 → Rˣ)

example :
    dvrMilnorTameSymbol' R F 1
      (milnorKTupleSymbol (fun _ : Fin 2 => dvrFracUniformizer F hπ)) =
        milnorKTupleSymbol (fun _ : Fin 1 => (-1 : (IsLocalRing.ResidueField R)ˣ)) :=
  dvrMilnorTameSymbol'_tuple_uniformizers hπ 1

example {τ : R} (hτ : Irreducible τ) (n : ℕ) (x : MilnorKTheory F (n + 1))
    (hx : dvrMilnorTameSymbol' R F n x = 0) :
    dvrMilnorSpecialization hτ (n + 1) x = dvrMilnorSpecialization hπ (n + 1) x :=
  dvrMilnorSpecialization_eq_on_residue_kernel hπ hτ n x hx
