/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

import Colib.CategoryTheory.Functor.Rebase

import Colib.CategoryTheory.Waldhausen.Additivity.PushoutCofibrations
import Colib.CategoryTheory.Waldhausen.Additivity.CofiberEndpoint

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
namespace WaldhausenAdditivityPushoutTests
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (W : Structure D) {F G : C ⥤ D} (a : F ⟶ G) (ha : ∀ X, W.cof (a.app X))

example (f : Arrow C) :
    IsPushout (a.app f.left) (F.map f.hom) (sourceι W a ha f) (targetι W a ha f) :=
  pushoutFunctor_isPushout W a ha f

example (f : Arrow C) : W.cof (targetι W a ha f) := targetι_cof W a ha f

example (X : C) : (pushoutIdentityNatIso W a ha).hom.app X =
    comparison W a ha (Arrow.mk (𝟙 X)) := pushoutIdentityIso_hom W a ha X

example {f g : Arrow C} (φ : f ⟶ g)
    (h₀ : W.weq (F.map φ.left)) (h₁ : W.weq (G.map φ.left))
    (h₂ : W.weq (F.map φ.right)) : W.weq ((pushoutFunctor W a ha).map φ) :=
  pushoutFunctor_map_weak W a ha φ h₀ h₁ h₂

example (V : Structure C) (hF : IsExact V.cof V.weq W.cof W.weq F)
    (h : IsCofibrationTransformation W a V) {f g : Arrow C}
    (φ : f ⟶ g) (hl : V.cof φ.left) (hr : V.cof φ.right) :
    W.cof ((pushoutFunctor W a h.app_cof).map φ) :=
  pushoutFunctor_map_cof W a V hF h φ hl hr

example : HasBinaryCoproducts D := hasBinaryCoproducts W

variable (f : Arrow C) {H : D} (q : G.obj f.left ⟶ H)
    (hq : IsPushout (a.app f.left) (W.isZero.from_ (F.obj f.left)) q (W.isZero.to_ H))
    (hz : F.map f.hom = W.isZero.from_ (F.obj f.left) ≫ W.isZero.to_ (F.obj f.right))
    [HasBinaryCoproduct H (F.obj f.right)]

example : sourceι W a ha f ≫ (cofiberEndpointIso W a ha f q hq hz).hom =
    q ≫ coprod.inl := sourceι_cofiberEndpointIso W a ha f q hq hz

example : targetι W a ha f ≫ (cofiberEndpointIso W a ha f q hq hz).hom = coprod.inr :=
  targetι_cofiberEndpointIso W a ha f q hq hz

end WaldhausenAdditivityPushoutTests

section IndependentRebase

universe u₁ v₁ u₂ v₂
variable {C₁ : Type u₁} [Category.{v₁} C₁] {D₁ : Type u₂} [Category.{v₂} D₁]

example (F : Arrow C₁ ⥤ D₁) (c : Arrow C₁) (d : D₁) (e : F.obj c ≅ d) :
    (rebaseFunctor F c d e).obj c = d :=
  rebaseFunctor_obj_base F c d e

example (F : C₁ ⥤ D₁) (c : C₁) :
    rebaseFunctor F c (F.obj c) (Iso.refl _) = F :=
  rebaseFunctor_refl F c

end IndependentRebase
