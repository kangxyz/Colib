/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.IteratedFiberEntry

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/IteratedFiberEquivalence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Strict fibers of the iterated second projection -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- Original fiber arrows are faithfully represented in the actual localization. -/
theorem secondFiberHom_injective (X : D)
    [(MonoidalLeftAction.actionRight C X).Faithful] {A B : C} {f g : A ⟶ B}
    (h : secondFiberHom X f = secondFiberHom X g) : f = g := by
  apply (secondFiberEntry (C := C) X).map_injective
  exact Subtype.ext h

/-- Every arrow over an identity is a unique original fiber arrow. -/
theorem existsUnique_secondFiberHom (X : D)
    [(MonoidalLeftAction.actionRight C X).Faithful] {A B : C}
    (h : (⟨(A, X)⟩ : Localization C D) ⟶ ⟨(B, X)⟩)
    (hh : secondProjection.map h = 𝟙 (⟨X⟩ : ActionLocalization C D)) :
    ∃! f : A ⟶ B, secondFiberHom X f = h := by
  let h' : (secondFiberEntry X).obj A ⟶ (secondFiberEntry X).obj B :=
    ⟨h, by rw [← hh]; exact IsHomLift.map _ _⟩
  obtain ⟨f, hf⟩ := (secondFiberEntry X).map_surjective h'
  refine ⟨f, congrArg Subtype.val hf, ?_⟩
  intro g hg
  exact secondFiberHom_injective X (hg.trans (congrArg Subtype.val hf).symm)

variable [BraidedCategory C]
attribute [local instance] firstCoordinateLeftAction

instance iteratedStrictFiberEntry_faithful (X : D)
    [(MonoidalLeftAction.actionRight C X).Faithful] :
    (iteratedStrictFiberEntry (C := C) X).Faithful where
  map_injective {A B} f g h := by
    obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective A.obj B.obj f
    obtain ⟨t, rfl⟩ := ActionLocalization.mkHom_surjective A.obj B.obj g
    have hh := congrArg Subtype.val h
    change (iteratedFiberEntry X).map (mkHom r.denom r.map.1 r.map.2) =
      (iteratedFiberEntry X).map (mkHom t.denom t.map.1 t.map.2) at hh
    rw [iteratedFiberEntry_mkHom, iteratedFiberEntry_mkHom] at hh
    obtain ⟨e, he, hk⟩ := (mkHom_eq_iff _ _ _ _ _ _).1 hh
    apply (mkHom_eq_iff _ _ _ _ _ _).2
    refine ⟨e, he, ?_⟩
    rw [firstCoordinateLeftAction_actorMap] at hk
    erw [secondFiberHom_comp] at hk
    have hmap := secondFiberHom_injective X hk
    rw [braiding_naturality_right_assoc] at hmap
    exact (cancel_epi (β_ A.obj.2 r.denom).hom).1 hmap

instance iteratedStrictFiberEntry_full (X : D)
    [(MonoidalLeftAction.actionRight C X).Faithful] :
    (iteratedStrictFiberEntry (C := C) X).Full where
  map_surjective {A B} h := by
    let := h.property
    have hh := (IsHomLift.eq_of_isHomLift iteratedSecondProjection
      (𝟙 (⟨X⟩ : ActionLocalization C D)) h.val).symm
    obtain ⟨r, hr⟩ := ActionLocalization.mkHom_surjective
      ((iteratedFiberEntry X).obj A).obj ((iteratedFiberEntry X).obj B).obj h.val
    rw [← hr] at hh
    change iteratedSecondProjection.map (mkHom r.denom r.map.1 r.map.2) = _ at hh
    rw [iteratedSecondProjection_mkHom] at hh
    obtain ⟨k, hk, _⟩ := existsUnique_secondFiberHom X r.map.2 hh
    refine ⟨mkHom r.denom r.map.1 ((β_ A.obj.2 r.denom).inv ≫ k), ?_⟩
    apply Subtype.ext
    change (iteratedFiberEntry X).map
      (mkHom r.denom r.map.1 ((β_ A.obj.2 r.denom).inv ≫ k)) = h.val
    rw [iteratedFiberEntry_mkHom, Iso.hom_inv_id_assoc, hk]
    exact hr

instance iteratedStrictFiberEntry_essSurj (X : D) :
    (iteratedStrictFiberEntry (C := C) X).EssSurj where
  mem_essImage Y := by
    obtain ⟨⟨⟨A, ⟨B, Y⟩⟩⟩, h⟩ := Y
    have he : Y = X := congrArg ActionLocalization.obj h
    subst he
    exact ⟨⟨(A, B)⟩, ⟨Iso.refl _⟩⟩

instance iteratedStrictFiberEntry_isEquivalence (X : D)
    [(MonoidalLeftAction.actionRight C X).Faithful] :
    (iteratedStrictFiberEntry (C := C) X).IsEquivalence where

/-- The iterated projection has the actual group-completion category as strict
fiber. Orbit faithfulness is the only additional hypothesis used here. -/
def iteratedSecondFiberEquivalence (X : D)
    [(MonoidalLeftAction.actionRight C X).Faithful] :
    Localization C C ≌ Functor.Fiber (iteratedSecondProjection (C := C)) ⟨X⟩ :=
  (iteratedStrictFiberEntry X).asEquivalence

end CategoryTheory.GroupCompletion.Localization
