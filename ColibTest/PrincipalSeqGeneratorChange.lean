/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Koszul.PrincipalSeqGeneratorChange

open CategoryTheory CategoryTheory.Abelian

universe u w

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

example (a c r : R) :
    ((Koszul.singletonSeqQuotientIso (c * a)).hom ≫
      ModuleCat.principalQuotientMulMap a c ≫ (Koszul.singletonSeqQuotientIso a).inv)
      (Ideal.Quotient.mk (Ideal.span (Set.range (fun _ : Fin 1 => c * a))) r) =
        Ideal.Quotient.mk (Ideal.span (Set.range (fun _ : Fin 1 => a))) r := rfl

example (a c : R) (ha : IsSMulRegular R a) (hca : IsSMulRegular R (c * a))
    (hf : Koszul.IsKoszulRegular (fun _ : Fin 1 => a))
    (hcf : Koszul.IsKoszulRegular (fun _ : Fin 1 => c * a)) (N : ModuleCat.{u} R) (x : N) :
    (Ext.mk₀ ((Koszul.singletonSeqQuotientIso (c * a)).hom ≫
      ModuleCat.principalQuotientMulMap a c ≫ (Koszul.singletonSeqQuotientIso a).inv)).comp
      ((Koszul.seqProjectiveResolution (fun _ : Fin 1 => a) hf).extMk
        (Koszul.singletonSeqCoordinate a ≫
          ModuleCat.ofHom (LinearMap.toSpanSingleton R N x))
        2 rfl (by simp [reassoc_of% Koszul.singletonSeqCoordinate_cocycle]; rfl)) (zero_add 1) =
      (Koszul.seqProjectiveResolution (fun _ : Fin 1 => c * a) hcf).extMk
        (Koszul.singletonSeqCoordinate (c * a) ≫
          ModuleCat.ofHom (LinearMap.toSpanSingleton R N (c • x)))
        2 rfl (by simp [reassoc_of% Koszul.singletonSeqCoordinate_cocycle]; rfl) :=
  Koszul.singletonSeqExtMk_generatorChange a c ha hca hf hcf N x
