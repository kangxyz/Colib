/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.UnitArrowEquiv
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.SingleObj

/-!
Implementation provenance: `Quillen/CategoryTheory/GroupCompletion/FramedCharacter.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Characters on framed pairs in the diagonal-action category

Conjugation-invariant characters unchanged by translation define an actual
functor on pairs with a chosen coordinate frame. Original quotient arrows act
on frames through the proved bijection with original zero-to-pair arrows.
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
variable {A : Type w} [CommGroup A]
variable (χ : ∀ P : C, End P →* A)

/-- The character of a relative coordinate frame, based at its first coordinate. -/
def frameDifference {P Q : C} (r s : P ⟶ Q) : A := χ P (r ≫ inv s)

omit [MonoidalCategory C] [IsGroupoid C] in
/-- Characters into a commutative group preserve categorical-order products. -/
lemma character_comp {P : C} (g h : End P) : χ P (g ≫ h) = χ P g * χ P h := by
  change χ P (h * g) = _
  rw [map_mul, mul_comm]

omit [MonoidalCategory C] in
/-- Relative-frame character differences satisfy the actual cocycle identity. -/
lemma frameDifference_cocycle {P Q : C} (r s t : P ⟶ Q) :
    frameDifference χ r s * frameDifference χ s t = frameDifference χ r t := by
  rw [frameDifference, frameDifference, frameDifference, ← character_comp]
  congr 1
  simp

omit [MonoidalCategory C] in
/-- A frame has trivial relative character against itself. -/
lemma frameDifference_self {P Q : C} (r : P ⟶ Q) : frameDifference χ r r = 1 := by
  simp only [frameDifference, IsIso.hom_inv_id]
  exact map_one (χ P)

variable (hconj : ∀ {P Q : C} (f : P ⟶ Q) (g : End P),
    χ Q (inv f ≫ g ≫ f) = χ P g)
variable (htranslate : ∀ (S P : C) (g : End P), χ (S ⊗ P) (S ◁ g) = χ P g)

include hconj htranslate in
/-- Every original quotient arrow preserves character differences between frames. -/
lemma frameDifference_transport {P Q P' Q' : C}
    (a : (⟨P, Q⟩ : Localization C C) ⟶ ⟨P', Q'⟩) (r s : P ⟶ Q) :
    frameDifference χ (transportFrame a r) (transportFrame a s) =
      frameDifference χ r s := by
  obtain ⟨a, rfl⟩ := ActionLocalization.mkHom_surjective _ _ a
  rw [transportFrame_mkHom, transportFrame_mkHom]
  unfold frameDifference
  have he : (inv a.map.1 ≫ a.denom ◁ r ≫ a.map.2) ≫
      inv (inv a.map.1 ≫ a.denom ◁ s ≫ a.map.2) =
        inv a.map.1 ≫ a.denom ◁ (r ≫ inv s) ≫ a.map.1 := by
    rw [whiskerLeft_comp]
    have hi : a.denom ◁ inv s = inv (a.denom ◁ s) := (tensorLeft a.denom).map_inv s
    rw [hi]
    simp [Category.assoc]
  rw [he, hconj]
  exact htranslate a.denom P (r ≫ inv s)

/-- A pair supplied with an actual coordinate frame. -/
structure FramedPair (C : Type u) [Category.{v} C] where
  /-- First coordinate. -/
  left : C
  /-- Second coordinate. -/
  right : C
  /-- Original coordinate frame. -/
  frame : left ⟶ right

/-- Forget the chosen coordinate frame. -/
abbrev FramedPair.toLocalization (X : FramedPair C) : Localization C C := ⟨X.left, X.right⟩

instance : Category (FramedPair C) where
  Hom X Y := X.toLocalization ⟶ Y.toLocalization
  id X := 𝟙 X.toLocalization
  comp f g := f ≫ g

/-- The actual full inclusion of framed objects into the diagonal-action category. -/
def framedInclusion : FramedPair C ⥤ Localization C C where
  obj X := X.toLocalization
  map f := f

/-- The original quotient arrows define a genuine character on all framed pairs. -/
def framedCharacter : FramedPair C ⥤ SingleObj A where
  obj _ := SingleObj.star A
  map {X Y} f := frameDifference χ (transportFrame f X.frame) Y.frame
  map_id X := by
    change frameDifference χ (transportFrame (𝟙 X.toLocalization) X.frame) X.frame = 1
    rw [transportFrame_id, frameDifference_self]
  map_comp {X Y Z} f g := by
    change frameDifference χ (transportFrame (f ≫ g) X.frame) Z.frame =
      frameDifference χ (transportFrame g Y.frame) Z.frame *
        frameDifference χ (transportFrame f X.frame) Y.frame
    rw [transportFrame_comp, mul_comm]
    rw [← frameDifference_transport χ hconj htranslate g (transportFrame f X.frame) Y.frame]
    exact (frameDifference_cocycle χ _ _ _).symm

/-- The diagonal pair equipped with its original identity frame. -/
def diagonalFrame (P : C) : FramedPair C := ⟨P, P, 𝟙 P⟩

/-- The framed character retains the original numerator automorphism value. -/
lemma framedCharacter_numerator (P : C) (g : End P) :
    (framedCharacter χ hconj htranslate).map
      (show diagonalFrame P ⟶ diagonalFrame P from ActionLocalization.ofHom (𝟙 P, g)) =
      χ P g := by
  change frameDifference χ (transportFrame (ActionLocalization.ofHom (𝟙 P, g)) (𝟙 P))
    (𝟙 P) = _
  rw [transportFrame_ofHom]
  simp [frameDifference]

/-- Original translations between diagonal frames have trivial character. -/
lemma framedCharacter_translation (S P : C) :
    (framedCharacter χ hconj htranslate).map
      (show diagonalFrame P ⟶ diagonalFrame (S ⊗ P) from
        ActionLocalization.translation S (P, P)) = 1 := by
  change frameDifference χ (transportFrame (ActionLocalization.translation S (P, P)) (𝟙 P))
    (𝟙 (S ⊗ P)) = 1
  rw [transportFrame_translation, whiskerLeft_id, frameDifference_self]

end CategoryTheory.GroupCompletion.Localization
