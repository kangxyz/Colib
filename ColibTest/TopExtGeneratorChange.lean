/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Koszul.TopExtGeneratorChange

open CategoryTheory CategoryTheory.Abelian

universe u w

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

example {n : ℕ} (f : Fin n → R) (M : Matrix (Fin n) (Fin n) R) (r : R) :
    Koszul.seqQuotientMatrixMap f M
      (Ideal.Quotient.mk (Ideal.span (Set.range (M.mulVec f))) r) =
        Ideal.Quotient.mk (Ideal.span (Set.range f)) r := rfl

example (f : Fin 2 → R) (M : Matrix (Fin 2) (Fin 2) R)
    (hf : Koszul.IsKoszulRegular f) (hMf : Koszul.IsKoszulRegular (M.mulVec f))
    (N : ModuleCat.{u} R) (x : N) :
    (Ext.mk₀ (Koszul.seqQuotientMatrixMap f M)).comp
      (Koszul.seqTopExtClass f hf N x) (zero_add 2) =
        Koszul.seqTopExtClass (M.mulVec f) hMf N (M.det • x) :=
  Koszul.seqTopExtClass_generatorChange f M hf hMf N x

example {n : ℕ} (f : Fin n → R) (M : Matrix (Fin n) (Fin n) R)
    (hf : Koszul.IsKoszulRegular f) (hMf : Koszul.IsKoszulRegular (M.mulVec f))
    (N : ModuleCat.{u} R) (x : N) :
    (Ext.mk₀ (Koszul.seqQuotientMatrixMap f M)).comp
      (Koszul.seqTopExtClass f hf N x) (zero_add n) =
        Koszul.seqTopExtClass (M.mulVec f) hMf N (M.det • x) :=
  Koszul.seqTopExtClass_generatorChange f M hf hMf N x

-- Empty matrices and empty sequences are included without a positive-degree hypothesis.
example (f : Fin 0 → R) (M : Matrix (Fin 0) (Fin 0) R)
    (hf : Koszul.IsKoszulRegular f) (hMf : Koszul.IsKoszulRegular (M.mulVec f))
    (N : ModuleCat.{u} R) (x : N) :
    (Ext.mk₀ (Koszul.seqQuotientMatrixMap f M)).comp
      (Koszul.seqTopExtClass f hf N x) (zero_add 0) =
        Koszul.seqTopExtClass (M.mulVec f) hMf N (M.det • x) :=
  Koszul.seqTopExtClass_generatorChange f M hf hMf N x
