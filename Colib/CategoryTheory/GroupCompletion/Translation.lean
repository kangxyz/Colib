/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.Functoriality
public import Colib.CategoryTheory.GroupCompletion.DiagonalAction
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/Translation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Translations on Grayson's group-completion category

Right tensor products commute with the diagonal left action by the actual
associator. They therefore induce translation functors on `C⁻¹C` without
strictifying the monoidal category.
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction

namespace CategoryTheory.GroupCompletion.Localization

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Right tensor translation of each coordinate before passing to the quotient. -/
def pairRightTensor (a b : C) : C × C ⥤ C × C :=
  (tensorRight a).prod (tensorRight b)

instance pairRightTensorLinear (a b : C) : (pairRightTensor a b).LaxLeftLinear C where
  μₗ s X := ((α_ s X.1 a).inv, (α_ s X.2 b).inv)
  μₗ_naturality_left f X := Prod.ext
    (associator_inv_naturality_left f X.1 a)
    (associator_inv_naturality_left f X.2 b)
  μₗ_naturality_right s _ _ f := Prod.ext
    (associator_inv_naturality_middle s f.1 a)
    (associator_inv_naturality_middle s f.2 b)
  μₗ_associativity s t X := by
    apply Prod.ext
    · exact pentagon_hom_inv_inv_inv_hom.symm
    · exact pentagon_hom_inv_inv_inv_hom.symm
  μₗ_unitality X := Prod.ext (leftUnitor_tensor_hom X.1 a) (leftUnitor_tensor_hom X.2 b)

/-- Simultaneously right-translate the two coordinates of `C⁻¹C`. -/
def rightTranslation (a b : C) : Localization C C ⥤ Localization C C :=
  ActionLocalization.mapFunctor (pairRightTensor a b)

@[simp]
lemma rightTranslation_obj (a b : C) (X : Localization C C) :
    (rightTranslation a b).obj X = ⟨X.obj.1 ⊗ a, X.obj.2 ⊗ b⟩ := rfl

/-- Translate only the first coordinate before localization. -/
def firstRightTensor (s : C) : C × C ⥤ C × C := (tensorRight s).prod (𝟭 C)

/-- Translate only the second coordinate before localization. -/
def secondRightTensor (s : C) : C × C ⥤ C × C := (𝟭 C).prod (tensorRight s)

instance firstRightTensorLinear (s : C) : (firstRightTensor s).LaxLeftLinear C where
  μₗ t X := ((α_ t X.1 s).inv, 𝟙 _)
  μₗ_naturality_left f X := by
    apply Prod.ext
    · exact associator_inv_naturality_left f X.1 s
    · change (f ▷ X.2) ≫ 𝟙 _ = 𝟙 _ ≫ (f ▷ X.2)
      simp
  μₗ_naturality_right t _ _ f := by
    apply Prod.ext
    · exact associator_inv_naturality_middle t f.1 s
    · change (t ◁ f.2) ≫ 𝟙 _ = 𝟙 _ ≫ (t ◁ f.2)
      simp
  μₗ_associativity t r X := by
    apply Prod.ext
    · exact pentagon_hom_inv_inv_inv_hom.symm
    · change 𝟙 _ ≫ (α_ t r X.2).hom = (α_ t r X.2).hom ≫ t ◁ 𝟙 _ ≫ 𝟙 _
      simp
  μₗ_unitality X := by
    apply Prod.ext
    · exact leftUnitor_tensor_hom X.1 s
    · change (λ_ X.2).hom = 𝟙 _ ≫ (λ_ X.2).hom
      simp

instance secondRightTensorLinear (s : C) : (secondRightTensor s).LaxLeftLinear C where
  μₗ t X := (𝟙 _, (α_ t X.2 s).inv)
  μₗ_naturality_left f X := by
    apply Prod.ext
    · change (f ▷ X.1) ≫ 𝟙 _ = 𝟙 _ ≫ (f ▷ X.1)
      simp
    · exact associator_inv_naturality_left f X.2 s
  μₗ_naturality_right t _ _ f := by
    apply Prod.ext
    · change (t ◁ f.1) ≫ 𝟙 _ = 𝟙 _ ≫ (t ◁ f.1)
      simp
    · exact associator_inv_naturality_middle t f.2 s
  μₗ_associativity t r X := by
    apply Prod.ext
    · change 𝟙 _ ≫ (α_ t r X.1).hom = (α_ t r X.1).hom ≫ t ◁ 𝟙 _ ≫ 𝟙 _
      simp
    · exact pentagon_hom_inv_inv_inv_hom.symm
  μₗ_unitality X := by
    apply Prod.ext
    · change (λ_ X.1).hom = 𝟙 _ ≫ (λ_ X.1).hom
      simp
    · exact leftUnitor_tensor_hom X.2 s

/-- Right translation of the first coordinate in `C⁻¹C`. -/
def firstTranslation (s : C) : Localization C C ⥤ Localization C C :=
  ActionLocalization.mapFunctor (firstRightTensor s)

/-- Right translation of the second coordinate in `C⁻¹C`. -/
def secondTranslation (s : C) : Localization C C ⥤ Localization C C :=
  ActionLocalization.mapFunctor (secondRightTensor s)

lemma firstTranslation_comp_secondTranslation (s t : C) :
    firstTranslation s ⋙ secondTranslation t = rightTranslation s t := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  change _ = 𝟙 ((rightTranslation s t).obj X) ≫ (rightTranslation s t).map f ≫
    𝟙 ((rightTranslation s t).obj Y)
  simp only [Category.id_comp, Category.comp_id]
  induction f using Quotient.inductionOn with
  | _ f => ?_
  change ActionLocalization.mkHom (X := (X.obj.1 ⊗ s, X.obj.2 ⊗ t))
    (Y := (Y.obj.1 ⊗ s, Y.obj.2 ⊗ t)) ⟨f.denom, _⟩ =
    ActionLocalization.mkHom ⟨f.denom, _⟩
  apply congrArg ActionLocalization.mkHom
  apply congrArg (ActionLocalization.HomRep.mk f.denom)
  apply Prod.ext
  · change 𝟙 _ ≫ ((α_ f.denom X.obj.1 s).inv ≫ f.map.1 ▷ s) =
      (α_ f.denom X.obj.1 s).inv ≫ f.map.1 ▷ s
    simp
  · change (α_ f.denom X.obj.2 t).inv ≫ (𝟙 _ ≫ f.map.2) ▷ t =
      (α_ f.denom X.obj.2 t).inv ≫ f.map.2 ▷ t
    simp

lemma secondTranslation_comp_firstTranslation (s t : C) :
    secondTranslation t ⋙ firstTranslation s = rightTranslation s t := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  change _ = 𝟙 ((rightTranslation s t).obj X) ≫ (rightTranslation s t).map f ≫
    𝟙 ((rightTranslation s t).obj Y)
  simp only [Category.id_comp, Category.comp_id]
  induction f using Quotient.inductionOn with
  | _ f => ?_
  change ActionLocalization.mkHom (X := (X.obj.1 ⊗ s, X.obj.2 ⊗ t))
    (Y := (Y.obj.1 ⊗ s, Y.obj.2 ⊗ t)) ⟨f.denom, _⟩ =
    ActionLocalization.mkHom ⟨f.denom, _⟩
  apply congrArg ActionLocalization.mkHom
  apply congrArg (ActionLocalization.HomRep.mk f.denom)
  apply Prod.ext
  · change (α_ f.denom X.obj.1 s).inv ≫ (𝟙 _ ≫ f.map.1) ▷ s =
      (α_ f.denom X.obj.1 s).inv ≫ f.map.1 ▷ s
    simp
  · change 𝟙 _ ≫ ((α_ f.denom X.obj.2 t).inv ≫ f.map.2 ▷ t) =
      (α_ f.denom X.obj.2 t).inv ≫ f.map.2 ▷ t
    simp

section Braided

variable [BraidedCategory C]

/-- The diagonal translation is naturally connected to the identity by the
arrow with translating object `s` and its two braidings. -/
def diagonalTranslationNatTrans (s : C) : 𝟭 (Localization C C) ⟶ rightTranslation s s where
  app X := mkHom s (β_ s X.obj.1).hom (β_ s X.obj.2).hom
  naturality := by
    rintro X Y ⟨f⟩
    apply Quotient.sound
    refine ⟨β_ s f.denom, ?_⟩
    apply Prod.ext
    · change (β_ s f.denom).hom ▷ X.obj.1 ≫
        ((α_ f.denom s X.obj.1).hom ≫ f.denom ◁ (β_ s X.obj.1).hom ≫
        ((α_ f.denom X.obj.1 s).inv ≫ f.map.1 ▷ s)) =
        (α_ s f.denom X.obj.1).hom ≫ s ◁ f.map.1 ≫ (β_ s Y.obj.1).hom
      rw [BraidedCategory.braiding_naturality_right]
      simp only [BraidedCategory.braiding_tensor_right_hom, Category.assoc,
        Iso.hom_inv_id_assoc]
    · change (β_ s f.denom).hom ▷ X.obj.2 ≫
        ((α_ f.denom s X.obj.2).hom ≫ f.denom ◁ (β_ s X.obj.2).hom ≫
        ((α_ f.denom X.obj.2 s).inv ≫ f.map.2 ▷ s)) =
        (α_ s f.denom X.obj.2).hom ≫ s ◁ f.map.2 ≫ (β_ s Y.obj.2).hom
      rw [BraidedCategory.braiding_naturality_right]
      simp only [BraidedCategory.braiding_tensor_right_hom, Category.assoc,
        Iso.hom_inv_id_assoc]

/-- The natural translation agrees with the canonical translation arrow
followed by the original pair of braidings. -/
lemma diagonalTranslationNatTrans_factorization (s : C) (X : Localization C C) :
    (diagonalTranslationNatTrans s).app X =
      ActionLocalization.translation s X.obj ≫
        ActionLocalization.ofHom ((β_ s X.obj.1).hom, (β_ s X.obj.2).hom) :=
  ActionLocalization.mkHom_factorization _

/-- At the diagonal unit, the translation is the original diagonal arrow
after identifying `unit ⊗ s` with `s` by the left unitors. -/
lemma diagonalTranslationNatTrans_unit (s : C) :
    (diagonalTranslationNatTrans s).app ⟨𝟙_ C, 𝟙_ C⟩ ≫
      ActionLocalization.ofHom (C := C) (X := (𝟙_ C ⊗ s, 𝟙_ C ⊗ s))
        (Y := (s, s)) ((λ_ s).hom, (λ_ s).hom) =
        mkHom (X := (𝟙_ C, 𝟙_ C)) (Y := (s, s)) s (ρ_ s).hom (ρ_ s).hom := by
  refine (ActionLocalization.mkHom_comp_ofHom
    (⟨s, ((β_ s (𝟙_ C)).hom, (β_ s (𝟙_ C)).hom)⟩ :
      ActionLocalization.HomRep (C := C) (𝟙_ C, 𝟙_ C) (𝟙_ C ⊗ s, 𝟙_ C ⊗ s))
    (((λ_ s).hom, (λ_ s).hom) : (𝟙_ C ⊗ s, 𝟙_ C ⊗ s) ⟶ (s, s))).trans ?_
  apply congrArg ActionLocalization.mkHom
  apply congrArg (ActionLocalization.HomRep.mk s)
  exact Prod.ext (braiding_leftUnitor s)
    (braiding_leftUnitor s)

/-- The first and second coordinate translations compose to a functor
naturally connected to the identity. -/
def firstSecondTranslationNatTrans (s : C) :
    𝟭 (Localization C C) ⟶ firstTranslation s ⋙ secondTranslation s := by
  rw [firstTranslation_comp_secondTranslation]
  exact diagonalTranslationNatTrans s

/-- The same connection in the opposite order. -/
def secondFirstTranslationNatTrans (s : C) :
    𝟭 (Localization C C) ⟶ secondTranslation s ⋙ firstTranslation s := by
  rw [secondTranslation_comp_firstTranslation]
  exact diagonalTranslationNatTrans s

end Braided

end CategoryTheory.GroupCompletion.Localization
