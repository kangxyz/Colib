/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Residue.Automorphism

/-!
Regression consumers of canonical residue equivariance. No Galois-extension or prime-degree
assumption is needed to restrict an individual actual fraction-field automorphism.
-/

noncomputable section

open Stacks.Chow IsLocalRing

universe u v w z

example {R : Type u} {S : Type v}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {F : Type w} {E : Type z} [Field F] [Field E]
    [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
    (j : R ≃+* S) (f : F →+* E)
    (hf : ∀ r : R, f (algebraMap R F r) = algebraMap S E (j r))
    (n : ℕ) (x : MilnorKTheory F (n + 1)) :
    dvrMilnorTameSymbol' S E n (milnorKTheoryMap f (n + 1) x) =
      milnorKTheoryMap (ResidueField.map (j : R →+* S)) n
        (dvrMilnorTameSymbol' R F n x) :=
  DFunLike.congr_fun (dvrMilnorTameSymbol'_map_ringEquiv j f hf n) x

variable (R S F E : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]

example (σ : Gal(E/F)) (n : ℕ) :
    letI : Algebra.IsAlgebraic F E := isAlgebraic_of_isFractionRing R S F E
    (dvrMilnorTameSymbol' S E n).comp
        (milnorKTheoryMap σ.toRingHom (n + 1)).toAddMonoidHom =
      (milnorKTheoryMap
        (ResidueField.map (galRestrict R F E S σ : S →+* S)) n).toAddMonoidHom.comp
          (dvrMilnorTameSymbol' S E n) :=
  dvrMilnorTameSymbol'_map_galRestrict R S F E σ n

example (σ : Gal(E/F)) (x : MilnorKTheory E 1) :
    letI : Algebra.IsAlgebraic F E := isAlgebraic_of_isFractionRing R S F E
    dvrMilnorTameSymbol' S E 0 (milnorKTheoryMap σ.toRingHom 1 x) =
      milnorKTheoryMap (ResidueField.map (galRestrict R F E S σ : S →+* S)) 0
        (dvrMilnorTameSymbol' S E 0 x) := by
  let : Algebra.IsAlgebraic F E := isAlgebraic_of_isFractionRing R S F E
  exact DFunLike.congr_fun (dvrMilnorTameSymbol'_map_galRestrict R S F E σ 0) x

end
