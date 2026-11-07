/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.FramedCharacter
public import Colib.CategoryTheory.GroupCompletion.CommonDenominator

/-!
Implementation provenance: `Quillen/CategoryTheory/GroupCompletion/FramedCommonSquares.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Common right squares with genuinely framed targets

An original arrow out of a framed pair supplies an actual frame on its target.
Thus the proved common-denominator squares have framed apexes, without any
cancellation or invariant-basis-number hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory MonoidalCategory
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsGroupoid C]

/-- An original arrow from a framed source induces an actual frame on its target. -/
def targetFrame {Y : FramedPair C} {X : Localization C C} (a : Y.toLocalization ⟶ X) :
    FramedPair C := ⟨X.obj.1, X.obj.2, transportFrame a Y.frame⟩

/-- An original arrow from the zero pair supplies an actual coordinate frame. -/
def zeroArrowFrame {X : Localization C C}
    (a : (⟨𝟙_ C, 𝟙_ C⟩ : Localization C C) ⟶ X) : FramedPair C :=
  ⟨X.obj.1, X.obj.2, (unitArrowEquiv X.obj.1 X.obj.2).symm a⟩

variable [BraidedCategory C]

/-- Original common right multiples can always be chosen with an actual framed apex. -/
theorem exists_framed_common_right_multiple {X : Localization C C}
    {Y Z : FramedPair C} (f : X ⟶ Y.toLocalization) (g : X ⟶ Z.toLocalization) :
    ∃ W : FramedPair C, ∃ a : Y ⟶ W, ∃ b : Z ⟶ W,
      f ≫ (framedInclusion (C := C)).map a = g ≫ (framedInclusion (C := C)).map b := by
  obtain ⟨W, a, b, h⟩ := ActionLocalization.exists_common_right_multiple f g
  exact ⟨targetFrame a, a, b, h⟩

end CategoryTheory.GroupCompletion.Localization
