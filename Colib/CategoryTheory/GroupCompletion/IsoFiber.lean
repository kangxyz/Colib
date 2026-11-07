/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.Monoidal.Action.IsoFiber
public import Colib.CategoryTheory.GroupCompletion.LocalizationFunctoriality
public import Colib.CategoryTheory.GroupCompletion.TrivialAction

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/IsoFiber.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Isomorphism fibers and the original action localization -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u₁ v₁ u₂ v₂
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Functor.LaxLeftLinear
namespace CategoryTheory.GroupCompletion.Localization
variable {S : Type u} [Category.{v} S] [MonoidalCategory S]
  {C : Type u₁} [Category.{v₁} C] [MonoidalLeftAction S C]
  {B : Type u₂} [Category.{v₂} B]

/-- Only the original projection target carries the trivial action. -/
local instance trivialFiberTarget : MonoidalLeftAction S B := MonoidalLeftAction.trivial S B

variable (F : C ⥤ B) [F.LaxLeftLinear S]

/-- Descend the original equivariant projection, retaining its actual target. -/
def fiberProjection : Localization S C ⥤ B :=
  secondProjection ⋙ ActionLocalization.mapFunctor F ⋙
    ActionLocalization.TrivialAction.forgetFunctor S B

@[simp]
lemma fiberProjection_obj (X : Localization S C) : (fiberProjection F).obj X = F.obj X.obj.2 := rfl

@[simp]
lemma fiberProjection_mkHom {X Y : S × C} (s : S) (f : s ⊗ X.1 ⟶ Y.1)
    (g : s ⊙ₗ X.2 ⟶ Y.2) :
    (fiberProjection F).map (mkHom s f g) = μₗ F s X.2 ≫ F.map g := by
  unfold fiberProjection
  rw [Functor.comp_map, secondProjection_mkHom, Functor.comp_map,
    ActionLocalization.mapFunctor_mkHom,
    ActionLocalization.TrivialAction.forgetFunctor_map_mkHom]
  rfl

variable [∀ (s : S) (X : C), IsIso (μₗ F s X)] (b : B)
attribute [local instance] IsoFiber.monoidalLeftAction

/-- Forget the base isomorphism only after forming the original localized category. -/
def isoFiberForget : Localization S (IsoFiber F b) ⥤ Localization S C :=
  actedMapFunctor (IsoFiber.forget F b)

/-- The original structure isomorphisms form a natural isomorphism after descent. -/
def isoFiberProjectionIso : (Functor.const (Localization S (IsoFiber F b))).obj b ≅
    isoFiberForget F b ⋙ fiberProjection F :=
  NatIso.ofComponents (fun X ↦ asIso X.obj.2.obj.hom) (by
    intro X Y f
    obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective X.obj Y.obj f
    change 𝟙 b ≫ Y.obj.2.obj.hom = X.obj.2.obj.hom ≫
      (fiberProjection F).map ((isoFiberForget F b).map (mkHom r.denom r.map.1 r.map.2))
    unfold isoFiberForget
    rw [actedMapFunctor_mkHom]
    change 𝟙 b ≫ Y.obj.2.obj.hom = X.obj.2.obj.hom ≫
      (fiberProjection F).map (mkHom (X := (X.obj.1, X.obj.2.obj.right))
        (Y := (Y.obj.1, Y.obj.2.obj.right)) r.denom r.map.1 (𝟙 _ ≫ r.map.2.hom.right))
    rw [Category.id_comp, Category.id_comp, fiberProjection_mkHom]
    exact (StructuredArrow.w r.map.2.hom).symm.trans (Category.assoc _ _ _))

/-- The canonical functor from localization of the actual isomorphism fiber
to the actual isomorphism fiber of the localized projection. -/
def isoFiberEntry : Localization S (IsoFiber F b) ⥤ IsoFiber (fiberProjection (S := S) F) b :=
  IsoFiber.lift (fiberProjection F) b (isoFiberForget F b) (isoFiberProjectionIso F b)

instance isoFiberEntry_faithful : (isoFiberEntry (S := S) F b).Faithful where
  map_injective {X Y} f g h := by
    have h' := congrArg (fun k ↦ k.hom.right) h
    obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective X.obj Y.obj f
    obtain ⟨t, rfl⟩ := ActionLocalization.mkHom_surjective X.obj Y.obj g
    change ActionLocalization.mkHom
      (ActionLocalization.HomRep.mapRep (actedPairFunctor (IsoFiber.forget F b)) r) =
      ActionLocalization.mkHom
        (ActionLocalization.HomRep.mapRep (actedPairFunctor (IsoFiber.forget F b)) t) at h'
    obtain ⟨e, he⟩ := Quotient.exact h'
    apply Quotient.sound
    refine ⟨e, ?_⟩
    apply Prod.ext
    · have h₁ := congrArg _root_.Prod.fst he
      change e.hom ▷ X.obj.1 ≫ (𝟙 _ ≫ t.map.1) = 𝟙 _ ≫ r.map.1 at h₁
      simp only [Category.id_comp] at h₁
      exact h₁
    · apply IsoFiber.action_hom_ext F b
      have h₂ := congrArg _root_.Prod.snd he
      change e.hom ⊵ₗ X.obj.2.obj.right ≫ (𝟙 _ ≫ t.map.2.hom.right) =
        𝟙 _ ≫ r.map.2.hom.right at h₂
      simp only [Category.id_comp] at h₂
      exact h₂

instance isoFiberEntry_full : (isoFiberEntry (S := S) F b).Full where
  map_surjective {X Y} f := by
    obtain ⟨r, hr⟩ := ActionLocalization.mkHom_surjective
      ((isoFiberForget F b).obj X).obj ((isoFiberForget F b).obj Y).obj f.hom.right
    have hf := StructuredArrow.w f.hom
    change X.obj.2.obj.hom ≫ (fiberProjection F).map f.hom.right = Y.obj.2.obj.hom at hf
    rw [← hr] at hf
    change X.obj.2.obj.hom ≫ (fiberProjection F).map (mkHom r.denom r.map.1 r.map.2) = _ at hf
    rw [fiberProjection_mkHom] at hf
    let g : IsoFiber.actionObj F b r.denom X.obj.2 ⟶ Y.obj.2 :=
      ⟨StructuredArrow.homMk r.map.2 (by
        change (X.obj.2.obj.hom ≫ μₗ F r.denom X.obj.2.obj.right) ≫ F.map r.map.2 = _
        exact (Category.assoc _ _ _).trans hf)⟩
    refine ⟨mkHom r.denom r.map.1 g, ?_⟩
    apply IsoFiber.action_hom_ext (fiberProjection F) b
    change (actedMapFunctor (IsoFiber.forget F b)).map (mkHom r.denom r.map.1 g) = f.hom.right
    rw [actedMapFunctor_mkHom]
    change mkHom (X := (X.obj.1, X.obj.2.obj.right))
      (Y := (Y.obj.1, Y.obj.2.obj.right)) r.denom r.map.1 (𝟙 _ ≫ r.map.2) = _
    rw [Category.id_comp]
    exact hr

instance isoFiberEntry_essSurj : (isoFiberEntry (S := S) F b).EssSurj where
  mem_essImage U := by
    let X : Localization S (IsoFiber F b) :=
      ⟨(U.obj.right.obj.1, IsoFiber.mk F b U.obj.right.obj.2 (asIso U.obj.hom))⟩
    refine ⟨X, ⟨(isoFiberProperty (fiberProjection F) b).isoMk ?_⟩⟩
    refine StructuredArrow.isoMk (Iso.refl U.obj.right) ?_
    change U.obj.hom ≫ (fiberProjection F).map (𝟙 U.obj.right) = U.obj.hom
    rw [Functor.map_id, Category.comp_id]

instance isoFiberEntry_isEquivalence : (isoFiberEntry (S := S) F b).IsEquivalence where

/-- Localization commutes with the actual isomorphism fiber, preserving
its denominator and specified base isomorphism. -/
def isoFiberEquivalence : Localization S (IsoFiber F b) ≌ IsoFiber (fiberProjection (S := S) F) b :=
  (isoFiberEntry F b).asEquivalence

end CategoryTheory.GroupCompletion.Localization
