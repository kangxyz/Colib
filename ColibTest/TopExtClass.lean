/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Koszul.TopExtClass

open CategoryTheory CategoryTheory.Abelian

universe u w

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

example (f : Fin 2 → R) (hf : Koszul.IsKoszulRegular f) (N : ModuleCat.{u} R)
    (e : Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N 2) :
    ∃ x : N, Koszul.seqTopExtClass f hf N x = e :=
  Koszul.seqTopExtClass_surjective f hf N e

example {n : ℕ} (f : Fin n → R) (hf : Koszul.IsKoszulRegular f)
    (N : ModuleCat.{u} R) (r : R) (x y : N) :
    Koszul.seqTopExtClass f hf N (r • x + y) =
      r • Koszul.seqTopExtClass f hf N x + Koszul.seqTopExtClass f hf N y := by
  simp

example (n : ℕ) : Koszul.topEquiv R n (Koszul.topGen R n) = 1 :=
  Koszul.topEquiv_topGen

-- Empty sequences retain the degree-zero classification.
example (f : Fin 0 → R) (hf : Koszul.IsKoszulRegular f) (N : ModuleCat.{u} R)
    (e : Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N 0) :
    ∃ x : N, Koszul.seqTopExtClass f hf N x = e :=
  Koszul.seqTopExtClass_surjective f hf N e

example {n : ℕ} (f : Fin n → R) (hf : Koszul.IsKoszulRegular f)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') (x : N) :
    (Koszul.seqTopExtClass f hf N x).comp (Ext.mk₀ g) (add_zero n) =
      Koszul.seqTopExtClass f hf N' (g x) :=
  Koszul.seqTopExtClass_comp_mk₀ f hf g x

example {n : ℕ} (f : Fin n → R) (hf : Koszul.IsKoszulRegular f)
    (N : ModuleCat.{u} R) (m : ℕ) (hm : m + 1 = n) (x : N) :
    Koszul.seqTopExtClass f hf N x = 0 ↔
      ∃ g : (Koszul.seqComplex f).X m ⟶ N, (Koszul.seqComplex f).d n m ≫ g =
        (Koszul.topEquiv R n).toModuleIso.hom ≫
          ModuleCat.ofHom (LinearMap.toSpanSingleton R N x) :=
  Koszul.seqTopExtClass_eq_zero_iff f hf N m hm x

-- The comparison and top-coordinate square remain explicit assumptions.
example {n : ℕ} (f g : Fin n → R)
    (hf : Koszul.IsKoszulRegular f) (hg : Koszul.IsKoszulRegular g)
    (q : ModuleCat.of R (R ⧸ Ideal.span (Set.range g)) ⟶
      ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))
    (Φ : ProjectiveResolution.Hom (Koszul.seqProjectiveResolution g hg)
      (Koszul.seqProjectiveResolution f hf) q) (d : R)
    (hTop : Φ.hom.f n ≫ (Koszul.topEquiv R n).toModuleIso.hom =
      (Koszul.topEquiv R n).toModuleIso.hom ≫ ModuleCat.ofHom (LinearMap.lsmul R R d))
    (N : ModuleCat.{u} R) (x : N) :
    (Ext.mk₀ q).comp (Koszul.seqTopExtClass f hf N x) (zero_add n) =
      Koszul.seqTopExtClass g hg N (d • x) :=
  Koszul.seqTopExtClass_covariance f hf g hg q Φ d hTop N x
