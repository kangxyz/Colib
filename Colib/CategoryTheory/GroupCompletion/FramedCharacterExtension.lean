/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.FramedCharacterCancellation
public import Colib.CategoryTheory.GroupCompletion.FramedCommonSquares
public import Colib.CategoryTheory.GroupCompletion.UnitRoofs
public import Colib.CategoryTheory.Localization.CharacterExtension
public import Colib.CategoryTheory.Localization.RightReachable
public import Colib.CategoryTheory.ObjectProperty.ExtensionByConstant

/-!
Implementation provenance: `Quillen/CategoryTheory/GroupCompletion/FramedCharacterExtension.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Extending the actual framed character to the completion category

The genuine character-cancellation theorem supplies equality-level descent.
The extension uses actual common right targets on the zero-connected components
and is constant on every other component.
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
    χ Q (inv f ≫ g ≫ f) = χ P g)
variable (htranslate : ∀ (S P : C) (g : End P), χ (S ⊗ P) (S ◁ g) = χ P g)

/-- The actual union of components containing the original zero object. -/
abbrev zeroReachable : CategoryTheory.ObjectProperty (Localization C C) :=
  CategoryTheory.Localization.RightReachable (⟨𝟙_ C, 𝟙_ C⟩ : Localization C C)

/-- Framed pairs lie in the original zero-reachable component. -/
def framedReachableInclusion : FramedPair C ⥤ (zeroReachable (C := C)).FullSubcategory where
  obj X := ⟨X.toLocalization, X.toLocalization, ⟨𝟙 _⟩, ⟨unitArrow X.frame⟩⟩
  map f := CategoryTheory.ObjectProperty.homMk f

/-- Common right squares for the component inclusion have actual framed apexes. -/
lemma framedReachable_square {X : (zeroReachable (C := C)).FullSubcategory}
    {Y Z : FramedPair C} (f : X ⟶ framedReachableInclusion.obj Y)
    (g : X ⟶ framedReachableInclusion.obj Z) :
    Nonempty (CategoryTheory.Localization.CharacterExtension.Square
      framedReachableInclusion f g) := by
  obtain ⟨W, a, b, h⟩ := exists_framed_common_right_multiple f.hom g.hom
  exact ⟨⟨W, a, b, CategoryTheory.ObjectProperty.hom_ext _ h⟩⟩

/-- The already proved character cancellation applies to the component inclusion. -/
lemma framedReachable_cancel {X : (zeroReachable (C := C)).FullSubcategory}
    {Y Z : FramedPair C} (r : X ⟶ framedReachableInclusion.obj Y) (f g : Y ⟶ Z)
    (h : r ≫ framedReachableInclusion.map f = r ≫ framedReachableInclusion.map g) :
    (framedCharacter χ hconj htranslate).map f =
      (framedCharacter χ hconj htranslate).map g :=
  framedCharacter_cancel χ hconj htranslate r.hom f g (congrArg (fun k => k.hom) h)

/-- A chosen original common target supplies the frame used in the component extension. -/
def reachableFrame (X : (zeroReachable (C := C)).FullSubcategory) : FramedPair C :=
  zeroArrowFrame X.property.choose_spec.2.some

/-- The chosen arrow to the framed target is an actual original quotient arrow. -/
def reachableFrameArrow (X : (zeroReachable (C := C)).FullSubcategory) :
    X ⟶ framedReachableInclusion.obj (reachableFrame X) :=
  CategoryTheory.ObjectProperty.homMk X.property.choose_spec.1.some

/-- The original framed character extends to the actual zero-reachable full subcategory. -/
def componentCharacter : (zeroReachable (C := C)).FullSubcategory ⥤ SingleObj A :=
  CategoryTheory.Localization.CharacterExtension.extension framedReachableInclusion
    (framedCharacter χ hconj htranslate)
    (fun f g => framedReachable_square f g)
    (fun r f g h => framedReachable_cancel χ hconj htranslate r f g h)
    reachableFrame reachableFrameArrow

/-- The component extension retains the original framed functor up to its actual comparison. -/
def componentCharacterIso :
    framedReachableInclusion ⋙ componentCharacter χ hconj htranslate ≅
      framedCharacter χ hconj htranslate :=
  CategoryTheory.Localization.CharacterExtension.extensionIso framedReachableInclusion
    (framedCharacter χ hconj htranslate)
    (fun f g => framedReachable_square f g)
    (fun r f g h => framedReachable_cancel χ hconj htranslate r f g h)
    reachableFrame reachableFrameArrow

/-- The character extends to the entire original diagonal-action category. -/
def completionCharacter : Localization C C ⥤ SingleObj A :=
  CategoryTheory.ObjectProperty.extensionByConstant zeroReachable
    (componentCharacter χ hconj htranslate)
    (SingleObj.star A)
    (fun f => CategoryTheory.Localization.rightReachable_arrow_iff
      ActionLocalization.exists_common_right_multiple _ f)

/-- The entire-category character retains the original framed character. -/
def completionCharacterIso : framedInclusion ⋙ completionCharacter χ hconj htranslate ≅
    framedCharacter χ hconj htranslate :=
  (Functor.isoWhiskerLeft framedReachableInclusion
    (CategoryTheory.ObjectProperty.extensionByConstantIso zeroReachable
      (componentCharacter χ hconj htranslate) (SingleObj.star A)
      (fun f => CategoryTheory.Localization.rightReachable_arrow_iff
        ActionLocalization.exists_common_right_multiple _ f))) ≪≫
    componentCharacterIso χ hconj htranslate

/-- On original framed endomorphisms the extension agrees exactly, since the target is abelian. -/
lemma completionCharacter_end {X : FramedPair C} (f : X ⟶ X) :
    (completionCharacter χ hconj htranslate).map (framedInclusion.map f) =
      (framedCharacter χ hconj htranslate).map f := by
  have h := (completionCharacterIso χ hconj htranslate).hom.naturality f
  change (completionCharacterIso χ hconj htranslate).hom.app X *
      (completionCharacter χ hconj htranslate).map (framedInclusion.map f) =
    (framedCharacter χ hconj htranslate).map f *
      (completionCharacterIso χ hconj htranslate).hom.app X at h
  rw [mul_comm ((framedCharacter χ hconj htranslate).map f)] at h
  exact mul_left_cancel h

/-- The global functor lifts through the actual categorical groupoid localization. -/
def localizedCharacter : (⊤ : MorphismProperty (Localization C C)).Localization ⥤ SingleObj A :=
  CategoryTheory.Localization.Construction.lift (completionCharacter χ hconj htranslate)
    (fun _ _ _ _ => inferInstance)

/-- The lift retains every original quotient arrow. -/
lemma localizedCharacter_map {X Y : Localization C C} (f : X ⟶ Y) :
    (localizedCharacter χ hconj htranslate).map ((completionFunctor (C := C)).map f) =
      (completionCharacter χ hconj htranslate).map f := by
  change ((⊤ : MorphismProperty (Localization C C)).Q ⋙
    CategoryTheory.Localization.Construction.lift (completionCharacter χ hconj htranslate)
      (fun _ _ _ _ => inferInstance)).map f = _
  rw [CategoryTheory.Localization.Construction.fac]

/-- The actual zero-loop character on the genuine categorical completion. -/
def completionLoopCharacter :
    End ((completionFunctor (C := C)).obj ⟨𝟙_ C, 𝟙_ C⟩) →* A where
  toFun g := (localizedCharacter χ hconj htranslate).map g
  map_one' := (localizedCharacter χ hconj htranslate).map_id _
  map_mul' g h := (localizedCharacter χ hconj htranslate).map_comp h g

/-- Every original numerator loop has exactly its original automorphism character. -/
lemma completionLoopCharacter_numerator {P : C} (g : End P) :
    completionLoopCharacter χ hconj htranslate (numeratorLoop g) = χ P g := by
  let L := localizedCharacter χ hconj htranslate
  let F := completionCharacter χ hconj htranslate
  let j : (⟨P, P⟩ : Localization C C) ⟶ ⟨P, P⟩ :=
    ActionLocalization.ofHom (𝟙 P, g)
  have hg : F.map j = χ P g :=
    (completionCharacter_end χ hconj htranslate (X := diagonalFrame P) j).trans
      (framedCharacter_numerator χ hconj htranslate P g)
  change L.map ((completionFunctor (C := C)).map (unitArrow (𝟙 P)) ≫
    (completionFunctor (C := C)).map j ≫
      inv ((completionFunctor (C := C)).map (unitArrow (𝟙 P)))) = _
  simp only [L.map_comp, L.map_inv]
  simp only [L, localizedCharacter_map, SingleObj.inv_as_inv, SingleObj.comp_as_mul]
  change (F.map (unitArrow (𝟙 P)))⁻¹ * F.map j * F.map (unitArrow (𝟙 P)) = _
  rw [hg]
  simp [mul_comm]

end CategoryTheory.GroupCompletion.Localization
