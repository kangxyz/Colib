/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib

open CategoryTheory

example (k : Type*) [Field k] :
    GrothendieckGroup.fgModuleRankEquiv k
      (GrothendieckGroup.of (FGModuleCat.of k k)) = 1 := by simp

example (k : Type*) [Field k] (n : ℤ) :
    GrothendieckGroup.fgModuleRankEquiv k
      (n • GrothendieckGroup.of (FGModuleCat.of k k)) = n := by simp

example (k : Type*) [Field k] (t : TensorProduct ℤ (Additive kˣ) (Additive kˣ)) :
    MilnorK.K2.pairPresentationEquiv k (milnorKTwoToKGroup k t) =
      Submodule.Quotient.mk t := by simp

example (k : Type*) [Field k] :
    1 = (Module.length k k).toNat * Module.finrank k (IsLocalRing.ResidueField k) := by
  simpa using IsLocalRing.finrank_eq_length_mul_residueFinrank k k

example (k : Type*) [Field k] :
    Module.finrank k k = ∑ᶠ x : PrimeSpectrum k,
      (Module.length (Localization.AtPrime x.asIdeal) (Localization.AtPrime x.asIdeal)).toNat *
        Module.finrank k (IsLocalRing.ResidueField (Localization.AtPrime x.asIdeal)) :=
  IsArtinianRing.finrank_eq_finsum_length_mul_residueFinrank k k
