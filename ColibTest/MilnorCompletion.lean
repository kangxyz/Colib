/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Residue.Completion

/-! Tests of the actual adic completion, its fraction lift, and canonical residue.
The ring and its selected fraction field have independent universes. -/

noncomputable section

universe u v

open Stacks.Chow IsLocalRing

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]

attribute [local instance] dvrCompletion_isDomain dvrCompletion_isDiscreteValuationRing

local notation "C" => AdicCompletion (maximalIdeal R) R
local notation "Q" => FractionRing C
local notation "φ" => IsFractionRing.lift (A := R) (K := F)
  (g := algebraMap R Q) (dvrCompletionFraction_algebraMap_injective R)
local notation "jκ" => ResidueField.map (algebraMap R C)

-- The source's actual uniformizer is unchanged by the completion fraction triangle.
example (π : R) : φ (algebraMap R F π) = algebraMap C Q (algebraMap R C π) := by
  rw [IsFractionRing.lift_algebraMap, IsScalarTower.algebraMap_apply R C Q]

-- It is still a uniformizer of the actual completed ring.
example (π : R) (hπ : Irreducible π) : Irreducible (algebraMap R C π) := by
  refine (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr ?_
  rw [AdicCompletion.maximalIdeal_eq_map,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.map_span]
  simp

-- A map having the same triangle is the original native localization lift.
example (f : F →+* Q) (hf : ∀ r : R,
    f (algebraMap R F r) = algebraMap C Q (algebraMap R C r)) : φ = f :=
  dvrCompletionFractionLift_unique R F f hf

-- The actual degree-zero target receives the residue of arbitrary degree-one classes.
example (x : MilnorKTheory F 1) :
    milnorKTheoryMap jκ 0 (dvrMilnorTameSymbol' R F 0 x) =
      dvrMilnorTameSymbol' C Q 0 (milnorKTheoryMap φ 1 x) :=
  DFunLike.congr_fun (dvrMilnorTameSymbol'_completion R F 0) x

-- The same comparison holds for every class, not only tuple symbols.
example (n : ℕ) (x : MilnorKTheory F (n + 1)) :
    milnorKTheoryMap jκ n (dvrMilnorTameSymbol' R F n x) =
      dvrMilnorTameSymbol' C Q n (milnorKTheoryMap φ (n + 1) x) :=
  DFunLike.congr_fun (dvrMilnorTameSymbol'_completion R F n) x

example (n : ℕ) (x : MilnorKTheory F (n + 1)) :
    let e := RingEquiv.ofBijective jκ (AdicCompletion.residueField_map_bijective R)
    milnorKTheoryMap e.symm.toRingHom n
      (dvrMilnorTameSymbol' C Q n (milnorKTheoryMap φ (n + 1) x)) =
        dvrMilnorTameSymbol' R F n x :=
  dvrMilnorTameSymbol'_completion_identification R F n x

-- Both directions of the kernel criterion are tested on an arbitrary class.
example (n : ℕ) (x : MilnorKTheory F (n + 1)) :
    dvrMilnorTameSymbol' C Q n (milnorKTheoryMap φ (n + 1) x) = 0 ↔
      dvrMilnorTameSymbol' R F n x = 0 :=
  dvrMilnorTameSymbol'_completion_eq_zero_iff R F n x

example (x : MilnorKTheory F 1) :
    dvrMilnorTameSymbol' C Q 0 (milnorKTheoryMap φ 1 x) = 0 ↔
      dvrMilnorTameSymbol' R F 0 x = 0 :=
  dvrMilnorTameSymbol'_completion_eq_zero_iff R F 0 x
