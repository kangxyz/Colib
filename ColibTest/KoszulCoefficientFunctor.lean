/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.RingTheory.Koszul.CoefficientFunctor
import Mathlib.RingTheory.Regular.Category

/-! Tests of native objects, coefficient morphisms and short exact sequences. -/

open CategoryTheory
open scoped ExteriorAlgebra TensorProduct

universe u v

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

-- The functor does not replace the canonical complex by an isomorphic model.
example (M : ModuleCat.{v} R) :
    (Koszul.seqComplexTensorFunctor f).obj M = Koszul.seqComplexTensor f M := rfl

example {M N : ModuleCat.{v} R} (g : M ⟶ N) (n : ℕ)
    (x : ⋀[R]^n (Fin r → R)) (m : M) :
    ((Koszul.seqComplexTensorFunctor f).map g).f n (x ⊗ₜ[R] m) =
      x ⊗ₜ[R] g m := rfl

-- No flatness or regularity hypothesis on coefficients or on f.
example (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) :
    (S.map (Koszul.seqComplexTensorFunctor f)).ShortExact :=
  Koszul.seqComplexTensorFunctor_shortExact f S hS

-- The empty sequence and degree zero are included, with independent universes.
example (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) :
    ((S.map (Koszul.seqComplexTensorFunctor (Fin.elim0 : Fin 0 → R))).map
      (HomologicalComplex.eval _ _ 0)).ShortExact :=
  Koszul.seqComplexTensorFunctor_degreewise_shortExact _ S hS 0

-- Apply to the actual scalar-quotient short exact sequence, not a custom quotient.
example (M : ModuleCat.{v} R) (a : R) (ha : IsSMulRegular M a) :
    ((M.smulShortComplex a).map (Koszul.seqComplexTensorFunctor f)).ShortExact :=
  Koszul.seqComplexTensorFunctor_shortExact f _ ha.smulShortComplex_shortExact
