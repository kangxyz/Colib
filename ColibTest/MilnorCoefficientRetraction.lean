/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Residue.CoefficientRetraction

/-! Regression tests for the explicit coefficient-field retraction hypotheses. -/

open Stacks.Chow

universe u v w

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]
  {k : Type w} [Field k]

-- All homogeneous classes, without assuming a residue-field section exists.
example {π : R} (hπ : Irreducible π) (c : k →+* R) (n : ℕ) (x : MilnorKTheory k n) :
    dvrMilnorSpecialization hπ n (milnorKTheoryMap ((algebraMap R F).comp c) n x) =
      milnorKTheoryMap ((IsLocalRing.residue R).comp c) n x :=
  LinearMap.congr_fun (dvrMilnorSpecialization_baseField hπ c n) x

-- The split embedding is supplied as actual ring maps with their exact composition equation.
example (c : k →+* R) (g : IsLocalRing.ResidueField R →+* k)
    (hc : g.comp ((IsLocalRing.residue R).comp c) = RingHom.id k) (n : ℕ) :
    Function.Injective (milnorKTheoryMap ((algebraMap R F).comp c) n) :=
  milnorKTheoryMap_injective_of_dvr_coefficient_retraction c g hc n

-- Degree zero is included.
example (c : k →+* R) (g : IsLocalRing.ResidueField R →+* k)
    (hc : g.comp ((IsLocalRing.residue R).comp c) = RingHom.id k) :
    Function.Injective (milnorKTheoryMap ((algebraMap R F).comp c) 0) :=
  milnorKTheoryMap_injective_of_dvr_coefficient_retraction c g hc 0

-- The supplied residue-field retraction is an actual left inverse on every class.
example {π : R} (hπ : Irreducible π) (c : k →+* R)
    (g : IsLocalRing.ResidueField R →+* k)
    (hc : g.comp ((IsLocalRing.residue R).comp c) = RingHom.id k)
    (n : ℕ) (x : MilnorKTheory k n) :
    milnorKTheoryMap g n
        (dvrMilnorSpecialization hπ n
          (milnorKTheoryMap ((algebraMap R F).comp c) n x)) = x :=
  LinearMap.congr_fun (dvrMilnorSpecialization_baseField_retraction hπ c g hc n) x
