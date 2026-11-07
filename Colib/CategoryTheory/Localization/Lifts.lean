/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # Ordinary lifts through a localization

Adapted from Quillen/Aglib/CategoryTheory/Abelian/SerreClass/Lifts.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual isomorphism lifts form a
filtered (respectively cofiltered) category under a left (respectively right)
calculus of fractions.
-/

@[expose] public noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Localization

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- Among arrows from localized objects to `V`, select the isomorphisms. -/
def liftProperty (L : C ⥤ D) (V : D) : ObjectProperty (CostructuredArrow L V) :=
  fun X => IsIso X.hom

/-- Ordinary ambient lifts of one quotient object, with a specified quotient
identification. Morphisms are ambient maps compatible with that identification. -/
abbrev AuxiliaryLift (L : C ⥤ D) (V : D) := (liftProperty L V).FullSubcategory

variable (L : C ⥤ D) (V : D)

instance auxiliaryLift_structure_isIso (X : AuxiliaryLift L V) : IsIso X.obj.hom := X.property

/-- Build a lift from a specified identification with `V`. -/
def auxiliaryLiftMk {N : C} (e : L.obj N ≅ V) : AuxiliaryLift L V :=
  ⟨CostructuredArrow.mk e.hom, by dsimp [liftProperty]; infer_instance⟩

/-- Its underlying ambient object. -/
def auxiliaryLiftProjection : AuxiliaryLift L V ⥤ C :=
  (liftProperty L V).ι ⋙ CostructuredArrow.proj L V

/-- Every ambient arrow between lifts becomes invertible after localization. -/
instance auxiliaryLift_map_isIso {X Y : AuxiliaryLift L V} (f : X ⟶ Y) :
    IsIso (L.map f.hom.left) := by
  have h : L.map f.hom.left = X.obj.hom ≫ inv Y.obj.hom := by
    apply (cancel_mono Y.obj.hom).1
    simp [CostructuredArrow.w f.hom]
  rw [h]
  infer_instance

section FractionCalculus

variable (W : MorphismProperty C) [L.IsLocalization W]
include W

/-- A localization supplies at least one lift of every quotient object. -/
theorem auxiliaryLift_nonempty : Nonempty (AuxiliaryLift L V) := by
  have := Localization.essSurj L W
  exact ⟨auxiliaryLiftMk L V (L.objObjPreimageIso V)⟩

section Left

variable [W.HasLeftCalculusOfFractions]

/-- A left fraction for the comparison of two lifts produces a common
successor, with its quotient identification verified explicitly. -/
theorem auxiliaryLift_cocone_objs (X Y : AuxiliaryLift L V) :
    ∃ (Z : AuxiliaryLift L V) (_ : X ⟶ Z) (_ : Y ⟶ Z), True := by
  obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L W
    (X.obj.hom ≫ inv Y.obj.hom)
  let e : L.obj φ.Y' ≅ V := (asIso (L.map φ.s)).symm ≪≫ asIso Y.obj.hom
  let Z := auxiliaryLiftMk L V e
  refine ⟨Z, ObjectProperty.homMk (CostructuredArrow.homMk φ.f ?_),
    ObjectProperty.homMk (CostructuredArrow.homMk φ.s ?_), trivial⟩
  · change L.map φ.f ≫ inv (L.map φ.s) ≫ Y.obj.hom = X.obj.hom
    have h := congrArg (fun k => k ≫ Y.obj.hom) hφ
    simpa [MorphismProperty.LeftFraction.map, Category.assoc] using h.symm
  · change L.map φ.s ≫ inv (L.map φ.s) ≫ Y.obj.hom = Y.obj.hom
    simp

/-- Equality after localization can be cleared by an actual denominator,
which coequalizes any two parallel lift arrows. -/
theorem auxiliaryLift_cocone_maps {X Y : AuxiliaryLift L V} (f g : X ⟶ Y) :
    ∃ (Z : AuxiliaryLift L V) (h : Y ⟶ Z), f ≫ h = g ≫ h := by
  have hfg : L.map f.hom.left = L.map g.hom.left := by
    apply (cancel_mono Y.obj.hom).1
    exact (CostructuredArrow.w f.hom).trans (CostructuredArrow.w g.hom).symm
  obtain ⟨N, s, hs, h⟩ := (MorphismProperty.map_eq_iff_postcomp L W _ _).1 hfg
  let e : L.obj N ≅ V := (Localization.isoOfHom L W s hs).symm ≪≫ asIso Y.obj.hom
  let Z := auxiliaryLiftMk L V e
  let h' : Y ⟶ Z := ObjectProperty.homMk (CostructuredArrow.homMk s (by
    change L.map s ≫ (Localization.isoOfHom L W s hs).inv ≫ Y.obj.hom = Y.obj.hom
    simp))
  refine ⟨Z, h', ?_⟩
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  exact h

/-- The actual auxiliary category of lifts is filtered. The proof uses both
existence of fraction representatives and equality after clearing denominators. -/
theorem auxiliaryLift_isFiltered : IsFiltered (AuxiliaryLift L V) where
  cocone_objs := auxiliaryLift_cocone_objs L V W
  cocone_maps := fun {_ _} f g => auxiliaryLift_cocone_maps L V W f g
  nonempty := auxiliaryLift_nonempty L V W

end Left

section Right

variable [W.HasRightCalculusOfFractions]

/-- A right fraction produces a common predecessor of any two lifts. -/
theorem auxiliaryLift_cone_objs (X Y : AuxiliaryLift L V) :
    ∃ (Z : AuxiliaryLift L V) (_ : Z ⟶ X) (_ : Z ⟶ Y), True := by
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L W
    (X.obj.hom ≫ inv Y.obj.hom)
  let e : L.obj φ.X' ≅ V := asIso (L.map φ.s) ≪≫ asIso X.obj.hom
  let Z := auxiliaryLiftMk L V e
  refine ⟨Z, ObjectProperty.homMk (CostructuredArrow.homMk φ.s rfl),
    ObjectProperty.homMk (CostructuredArrow.homMk φ.f ?_), trivial⟩
  change L.map φ.f ≫ Y.obj.hom = L.map φ.s ≫ X.obj.hom
  have h := congrArg (fun k => L.map φ.s ≫ k ≫ Y.obj.hom) hφ
  simpa [MorphismProperty.RightFraction.map, Category.assoc] using h.symm

/-- The right calculus clears equality by an actual common predecessor. -/
theorem auxiliaryLift_cone_maps {X Y : AuxiliaryLift L V} (f g : X ⟶ Y) :
    ∃ (Z : AuxiliaryLift L V) (h : Z ⟶ X), h ≫ f = h ≫ g := by
  have hfg : L.map f.hom.left = L.map g.hom.left := by
    apply (cancel_mono Y.obj.hom).1
    exact (CostructuredArrow.w f.hom).trans (CostructuredArrow.w g.hom).symm
  obtain ⟨N, s, hs, h⟩ := (MorphismProperty.map_eq_iff_precomp L W _ _).1 hfg
  let e : L.obj N ≅ V := Localization.isoOfHom L W s hs ≪≫ asIso X.obj.hom
  let Z := auxiliaryLiftMk L V e
  let h' : Z ⟶ X := ObjectProperty.homMk (CostructuredArrow.homMk s rfl)
  refine ⟨Z, h', ?_⟩
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  exact h

/-- With the right calculus, the same ordinary lift category is cofiltered. -/
theorem auxiliaryLift_isCofiltered : IsCofiltered (AuxiliaryLift L V) where
  cone_objs := auxiliaryLift_cone_objs L V W
  cone_maps := fun {_ _} f g => auxiliaryLift_cone_maps L V W f g
  nonempty := auxiliaryLift_nonempty L V W

end Right
end FractionCalculus


end CategoryTheory.Localization
