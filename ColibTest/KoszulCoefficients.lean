/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Koszul.Coefficients

open CategoryTheory
open scoped ExteriorAlgebra

universe u

variable {R : Type u} [CommRing R] {r : ℕ}

example (f : Fin r → R) (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    Module.Finite R ((Koszul.seqComplexTensor f M).X n) := inferInstance

example [IsNoetherianRing R] (f : Fin r → R) (M : ModuleCat.{u} R)
    [Module.Finite R M] (n : ℕ) :
    Module.Finite R ((Koszul.seqComplexTensor f M).homology n) := inferInstance

-- Annihilation imposes no finiteness, Noetherianity, or regularity assumption.
example (f : Fin r → R) (M : ModuleCat.{u} R) (n : ℕ) :
    Module.annihilator R M ≤ Module.annihilator R ((Koszul.seqComplexTensor f M).homology n) :=
  Koszul.annihilator_le_annihilator_seqComplexTensor_homology f M n

-- The ring-term finiteness source instance is supplied by Mathlib exterior powers.
example (f : Fin r → R) (n : ℕ) : Module.Finite R ((Koszul.seqComplex f).X n) :=
  inferInstanceAs (Module.Finite R (⋀[R]^n (Fin r → R)))

-- Test the stronger Noetherian instance itself, not only its finite-module consequence.
example [IsNoetherianRing R] (f : Fin r → R) (M : ModuleCat.{u} R)
    [Module.Finite R M] (n : ℕ) :
    IsNoetherian R ((Koszul.seqComplexTensor f M).homology n) := inferInstance

example (f : Fin r → R) (M : ModuleCat.{u} R) (n : ℕ) :
    Module.annihilator R M ≤ Module.annihilator R ((Koszul.seqComplexTensor f M).X n) :=
  Koszul.annihilator_le_annihilator_seqComplexTensor_X f M n

-- No nonempty-sequence assumption is present.
example (M : ModuleCat.{u} R) (n : ℕ) :
    Module.annihilator R M ≤
      Module.annihilator R ((Koszul.seqComplexTensor (Fin.elim0 : Fin 0 → R) M).homology n) :=
  Koszul.annihilator_le_annihilator_seqComplexTensor_homology _ M n
