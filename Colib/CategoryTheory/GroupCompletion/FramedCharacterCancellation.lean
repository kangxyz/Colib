/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.FramedCharacter
public import Colib.CategoryTheory.GroupCompletion.Translation

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/FramedCharacterCancellation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Character cancellation without categorical cancellation

Translate a given equality by the denominator of its first arrow. Its source
then acquires an actual frame. Cancellation in the target groupoid and the
original translation natural transformation give character cancellation only.
No Ore cancellation or cancellation of projective summands is asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory MonoidalCategory
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsGroupoid C]
  [BraidedCategory C]
variable {A : Type w} [CommGroup A]
variable (χ : ∀ P : C, End P →* A)
variable (hconj : ∀ {P Q : C} (f : P ⟶ Q) (g : End P),
    χ Q (End.of (inv f ≫ g.asHom ≫ f)) = χ P g)
variable (htranslate : ∀ (S P : C) (g : End P), χ (S ⊗ P) (End.of (S ◁ g.asHom)) = χ P g)

/-- Original right translation carries each chosen frame to its right tensor translate. -/
def framedRightTranslation (S : C) : FramedPair C ⥤ FramedPair C where
  obj X := ⟨X.left ⊗ S, X.right ⊗ S, X.frame ▷ S⟩
  map f := (rightTranslation S S).map f
  map_id X := (rightTranslation S S).map_id X.toLocalization
  map_comp f g := (rightTranslation S S).map_comp f g

/-- The original diagonal-translation natural transformation lifts to framed pairs. -/
def framedTranslationNatTrans (S : C) : 𝟭 (FramedPair C) ⟶ framedRightTranslation S where
  app X := (diagonalTranslationNatTrans S).app X.toLocalization
  naturality := by
    intro X Y f
    exact (diagonalTranslationNatTrans S).naturality f

/-- The original translation component takes the source frame exactly to the translated frame. -/
lemma transportFrame_diagonalTranslation (S : C) (X : FramedPair C) :
    transportFrame ((diagonalTranslationNatTrans S).app X.toLocalization) X.frame =
      X.frame ▷ S := by
  change transportFrame (ActionLocalization.mkHom
    (⟨S, ((β_ S X.left).hom, (β_ S X.right).hom)⟩ :
      ActionLocalization.HomRep (X.left, X.right) (X.left ⊗ S, X.right ⊗ S))) X.frame = _
  rw [transportFrame_mkHom]
  change inv (β_ S X.left).hom ≫ S ◁ X.frame ≫ (β_ S X.right).hom = _
  rw [BraidedCategory.braiding_naturality_right]
  simp

/-- The natural translation components have trivial character for the translated frames. -/
lemma framedCharacter_translation_component (S : C) (X : FramedPair C) :
    (framedCharacter χ hconj htranslate).map ((framedTranslationNatTrans S).app X) = 1 := by
  change frameDifference χ
    (transportFrame ((diagonalTranslationNatTrans S).app X.toLocalization) X.frame)
      (X.frame ▷ S) = 1
  rw [transportFrame_diagonalTranslation, frameDifference_self]

/-- Original right translation leaves the character of each framed arrow unchanged. -/
lemma framedCharacter_rightTranslation (S : C) {X Y : FramedPair C} (f : X ⟶ Y) :
    (framedCharacter χ hconj htranslate).map ((framedRightTranslation S).map f) =
      (framedCharacter χ hconj htranslate).map f := by
  let F := framedCharacter χ hconj htranslate
  have h := congrArg (fun k => F.map k) ((framedTranslationNatTrans S).naturality f)
  rw [F.map_comp, F.map_comp] at h
  change F.map f ≫ F.map ((framedTranslationNatTrans S).app Y) =
    F.map ((framedTranslationNatTrans S).app X) ≫ F.map ((framedRightTranslation S).map f) at h
  rw [framedCharacter_translation_component, framedCharacter_translation_component] at h
  change 1 * F.map f = F.map ((framedRightTranslation S).map f) * 1 at h
  simpa only [one_mul, mul_one] using h.symm

/-- Cancellation holds for the character, even when it fails for the original category. -/
theorem framedCharacter_cancel {X : Localization C C} {Y Z : FramedPair C}
    (r : X ⟶ Y.toLocalization) (f g : Y ⟶ Z)
    (h : r ≫ (framedInclusion (C := C)).map f =
      r ≫ (framedInclusion (C := C)).map g) :
    (framedCharacter χ hconj htranslate).map f =
      (framedCharacter χ hconj htranslate).map g := by
  obtain ⟨a, rfl⟩ := ActionLocalization.mkHom_surjective _ _ r
  let S := a.denom
  let T := rightTranslation S S
  let W : FramedPair C :=
    ⟨X.obj.1 ⊗ S, X.obj.2 ⊗ S,
      (β_ S X.obj.1).inv ≫ a.map.1 ≫ Y.frame ≫ inv a.map.2 ≫ (β_ S X.obj.2).hom⟩
  let r' : W ⟶ (framedRightTranslation S).obj Y := T.map (ActionLocalization.mkHom a)
  have he : r' ≫ (framedRightTranslation S).map f =
      r' ≫ (framedRightTranslation S).map g := by
    exact ((T.map_comp _ _).symm.trans (congrArg (fun k => T.map k) h)).trans
      (T.map_comp _ _)
  let F := framedCharacter χ hconj htranslate
  have hf := congrArg (fun k => F.map k) he
  rw [F.map_comp, F.map_comp] at hf
  have hg : F.map ((framedRightTranslation S).map f) =
      F.map ((framedRightTranslation S).map g) := (cancel_epi (F.map r')).mp hf
  rw [framedCharacter_rightTranslation, framedCharacter_rightTranslation] at hg
  exact hg

end CategoryTheory.GroupCompletion.Localization
