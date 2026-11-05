/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Koszul.PrincipalGeneratorTransport

open CategoryTheory CategoryTheory.Abelian

universe u w

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
  (a : R) (ha : IsSMulRegular R a) {Q : ModuleCat.{u} R} (P : ProjectiveResolution Q)
  (e : Q ≅ ModuleCat.of R (R ⧸ Ideal.span {a}))
  (b : P.complex.X 0 ⟶ ModuleCat.of R R) (c : P.complex.X 1 ⟶ ModuleCat.of R R)
  (hc : P.complex.d 2 1 ≫ c = 0)
  (h : c ≫ ModuleCat.ofHom (LinearMap.lsmul R R a) = P.complex.d 1 0 ≫ b)
  (hb : b ≫ ModuleCat.ofHom (Ideal.span {a}).mkQ = P.π.f 0 ≫ e.hom)

example (N : ModuleCat.{u} R) (x : N) :
    (Ext.mk₀ e.inv).comp
      (P.extMk (c ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R N x)) 2 rfl
        (by simp [reassoc_of% hc])) (zero_add 1) =
      -((ModuleCat.principalShortComplex_shortExact a ha).extClass.comp
        (Ext.mk₀ (ModuleCat.ofHom (LinearMap.toSpanSingleton R N x))) (add_zero 1)) := by
  simpa only [Koszul.principalExtOneClass_apply] using
    Koszul.principalExtMk_transport_eq_neg_class a ha P e b c hc h hb N x

example (N : ModuleCat.{u} R) (y : N) :
    (Ext.mk₀ e.inv).comp
      (P.extMk (c ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R N (a • y))) 2 rfl
        (by simp [reassoc_of% hc])) (zero_add 1) = 0 := by
  rw [Koszul.principalExtMk_transport_eq_neg_class a ha P e b c hc h hb N,
    (Koszul.principalExtOneClass_eq_zero_iff a ha N (a • y)).mpr ⟨y, rfl⟩, neg_zero]
