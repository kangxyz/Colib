/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Koszul.PrincipalSeqGenerator

open CategoryTheory CategoryTheory.Abelian

universe u w

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

example (a : R) (ha : IsSMulRegular R a)
    (hf : Koszul.IsKoszulRegular (fun _ : Fin 1 => a)) (N : ModuleCat.{u} R) (x : N) :
    (Ext.mk₀ (Koszul.singletonSeqQuotientIso a).inv).comp
      ((Koszul.seqProjectiveResolution (fun _ : Fin 1 => a) hf).extMk
        (Koszul.singletonSeqCoordinate a ≫
          ModuleCat.ofHom (LinearMap.toSpanSingleton R N x))
        2 rfl (by simp [reassoc_of% Koszul.singletonSeqCoordinate_cocycle]; rfl)) (zero_add 1) =
      -((ModuleCat.principalShortComplex_shortExact a ha).extClass.comp
        (Ext.mk₀ (ModuleCat.ofHom (LinearMap.toSpanSingleton R N x))) (add_zero 1)) := by
  exact Koszul.singletonSeqExtMk_eq_neg_class a ha hf N x

example (a : R) :
    Koszul.singletonSeqCoordinate a
      ((exteriorPower.oneEquiv R (Fin 1 → R)).symm (fun _ => 1)) = 1 := by
  change (exteriorPower.oneEquiv R (Fin 1 → R))
    ((exteriorPower.oneEquiv R (Fin 1 → R)).symm (fun _ => 1)) 0 = 1
  rw [LinearEquiv.apply_symm_apply]

example (a : R) (ha : IsSMulRegular R a) :
    Koszul.IsKoszulRegular (fun _ : Fin 1 => a) := by
  apply (Koszul.isKoszulRegularOn_self_iff _).mp
  apply Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular.1
  simpa [List.ofFn_succ, RingTheory.Sequence.isWeaklyRegular_cons_iff] using ha
