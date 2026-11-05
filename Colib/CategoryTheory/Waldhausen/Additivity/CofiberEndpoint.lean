/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Additivity.PushoutEndpoints
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-! # The zero-arrow endpoint of the actual additivity deformation

## Implementation provenance

Adapted from `Quillen/Waldhausen/Additivity/CofiberEndpoint.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original objects, maps,
universes and hypotheses are retained. This categorical input is not an
additivity theorem on realizations or K-groups.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v u' v'

namespace CategoryTheory.Waldhausen.Additivity

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (W : Structure D)

include W in
/-- Binary coproducts are supplied by the genuine Waldhausen pushout axiom. -/
theorem hasBinaryCoproduct (X Y : D) : HasBinaryCoproduct X Y := by
  obtain ⟨P, i, j, hs⟩ := W.pushout_exists (W.isZero.to_ X) (W.isZero.to_ Y) (W.cof_zero X)
  refine ⟨⟨BinaryCofan.mk i j, BinaryCofan.IsColimit.mk _
    (fun f g ↦ hs.desc f g (W.isZero.eq_of_src _ _)) ?_ ?_ ?_⟩⟩
  · intro T f g
    exact hs.inl_desc _ _ _
  · intro T f g
    exact hs.inr_desc _ _ _
  · intro T f g m hm hn
    apply hs.hom_ext
    · exact hm.trans (hs.inl_desc _ _ _).symm
    · exact hn.trans (hs.inr_desc _ _ _).symm

include W in
/-- No additional finite-coproduct assumption is needed for Waldhausen additivity. -/
theorem hasBinaryCoproducts : HasBinaryCoproducts D := by
  let {X Y : D} : HasBinaryCoproduct X Y := hasBinaryCoproduct W X Y
  exact hasBinaryCoproducts_of_hasColimit_pair D

variable {F G : C ⥤ D} (a : F ⟶ G) (ha : ∀ X, W.cof (a.app X))
variable (f : Arrow C) {H : D} (q : G.obj f.left ⟶ H)
variable (hq : IsPushout (a.app f.left) (W.isZero.from_ (F.obj f.left)) q (W.isZero.to_ H))
variable (hz : F.map f.hom = W.isZero.from_ (F.obj f.left) ≫ W.isZero.to_ (F.obj f.right))
variable [HasBinaryCoproduct H (F.obj f.right)]

include hq hz

/-- Pasting the actual cofiber square with a coproduct square identifies the
pushout of the zero arrow. -/
theorem cofiberEndpoint_isPushout :
    IsPushout (a.app f.left) (F.map f.hom)
      (q ≫ (coprod.inl : H ⟶ H ⨿ F.obj f.right)) coprod.inr := by
  have hs : IsPushout (W.isZero.to_ H) (W.isZero.to_ (F.obj f.right))
      (coprod.inl : H ⟶ H ⨿ F.obj f.right) coprod.inr := by
    have hH : W.isZero.isInitial.to H = W.isZero.to_ H := W.isZero.eq_of_src _ _
    have hF : W.isZero.isInitial.to (F.obj f.right) = W.isZero.to_ (F.obj f.right) :=
      W.isZero.eq_of_src _ _
    simpa only [hH, hF] using
      IsPushout.of_is_coproduct' (coprodIsCoprod H (F.obj f.right)) W.isZero.isInitial
  rw [hz]
  exact hq.paste_vert hs

/-- The zero-arrow endpoint is the sum of the quotient at the source and the
subobject functor at the target, with its actual categorical isomorphism. -/
def cofiberEndpointIso : (pushoutFunctor W a ha).obj f ≅ H ⨿ F.obj f.right := by
  letI := hasPushout W a ha f.hom
  exact (cofiberEndpoint_isPushout W a f q hq hz).isoPushout.symm

@[reassoc (attr := simp)]
theorem sourceι_cofiberEndpointIso :
    sourceι W a ha f ≫ (cofiberEndpointIso W a ha f q hq hz).hom = q ≫ coprod.inl := by
  let := hasPushout W a ha f.hom
  exact (cofiberEndpoint_isPushout W a f q hq hz).inl_isoPushout_inv

@[reassoc (attr := simp)]
theorem targetι_cofiberEndpointIso :
    targetι W a ha f ≫ (cofiberEndpointIso W a ha f q hq hz).hom = coprod.inr := by
  let := hasPushout W a ha f.hom
  exact (cofiberEndpoint_isPushout W a f q hq hz).inr_isoPushout_inv

end CategoryTheory.Waldhausen.Additivity
