/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.Projection
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/ProjectionComma.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The comma categories of the localization projection

The fiber entry has a left adjoint, constructed by transporting an object along
a chosen representative of its base arrow. Uniqueness of normal forms makes
this construction independent of all subsequent morphism choices.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsGroupoid C]
  [∀ A : C, (tensorRight A).Faithful]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- The original acted-on category inside a comma category over the projection. -/
def commaEntry (B : C) : D ⥤ CostructuredArrow (projection (D := D)) ⟨B⟩ where
  obj X := CostructuredArrow.mk (S := projection (C := C) (D := D))
    (Y := (⟨(B, X)⟩ : Localization C D)) (𝟙 (⟨B⟩ : ActionLocalization C C))
  map {X Y} g := CostructuredArrow.homMk
    (ActionLocalization.ofHom (X := (B, X)) (Y := (B, Y)) (𝟙 B, g)) (by
    change (ActionLocalization.mapFunctor (CategoryTheory.Prod.fst C D)).map
      (ActionLocalization.ofHom (X := (B, X)) (Y := (B, Y)) (𝟙 B, g)) ≫ 𝟙 _ = 𝟙 _
    rw [ActionLocalization.mapFunctor_ofHom]
    change ActionLocalization.ofHom (C := C) (𝟙 B) ≫ 𝟙 _ = 𝟙 _
    simp)
  map_id X := by
    apply CostructuredArrow.hom_ext
    exact ActionLocalization.ofHom_id (B, X)
  map_comp {X Y Z} f g := by
    apply CostructuredArrow.hom_ext
    simpa using ActionLocalization.ofHom_comp (C := C)
      (X := (B, X)) (Y := (B, Y)) (Z := (B, Z)) (𝟙 B, f) (𝟙 B, g)

/-- Choose only a representative of the base arrow. -/
def commaBaseRep {B : C} (U : CostructuredArrow (projection (D := D)) ⟨B⟩) :
    ActionLocalization.HomRep (C := C) U.left.obj.1 B :=
  (ActionLocalization.mkHom_surjective U.left.obj.1 B U.hom).choose

omit [IsGroupoid C] [∀ A : C, (tensorRight A).Faithful] in
lemma commaBaseRep_spec {B : C} (U : CostructuredArrow (projection (D := D)) ⟨B⟩) :
    ActionLocalization.mkHom (commaBaseRep U) = U.hom :=
  (ActionLocalization.mkHom_surjective U.left.obj.1 B U.hom).choose_spec

/-- The transported object uses the actual monoidal action. -/
abbrev commaTransportObj {B : C} (U : CostructuredArrow (projection (D := D)) ⟨B⟩) : D :=
  (commaBaseRep U).denom ⊙ₗ U.left.obj.2

/-- A map out of the transported object gives a comma arrow by its normal form. -/
def commaHom {B : C} (U : CostructuredArrow (projection (D := D)) ⟨B⟩)
    (Y : D) (g : commaTransportObj U ⟶ Y) : U ⟶ (commaEntry B).obj Y :=
  CostructuredArrow.homMk
    (mkHom (X := U.left.obj) (Y := (B, Y)) (commaBaseRep U).denom (commaBaseRep U).map g)
    (by
      change projection.map (mkHom (X := U.left.obj) (Y := (B, Y))
        (commaBaseRep U).denom (commaBaseRep U).map g) ≫ 𝟙 _ = U.hom
      rw [Category.comp_id, projection_mkHom, commaBaseRep_spec])

lemma commaHom_bijective {B : C}
    (U : CostructuredArrow (projection (D := D)) ⟨B⟩) (Y : D) :
    Function.Bijective (commaHom U Y) := by
  constructor
  · intro g g' h
    exact (mkHom_eq_iff_same_base (X := U.left.obj) (Y := (B, Y))
      (commaBaseRep U).denom (commaBaseRep U).map g g').1
      (congrArg (fun k ↦ k.left) h)
  · intro h
    have hh : projection.map h.left = ActionLocalization.mkHom (commaBaseRep U) := by
      rw [commaBaseRep_spec]
      simpa [commaEntry] using CostructuredArrow.w h
    obtain ⟨g, hg, _⟩ := existsUnique_normalized (X := U.left.obj) (Y := (B, Y))
      (commaBaseRep U).denom (commaBaseRep U).map h.left hh
    exact ⟨g, CostructuredArrow.hom_ext _ _ hg⟩

/-- Normal forms identify the comma hom set with maps out of the transported object. -/
def commaHomEquiv {B : C} (U : CostructuredArrow (projection (D := D)) ⟨B⟩) (Y : D) :
    (commaTransportObj U ⟶ Y) ≃ (U ⟶ (commaEntry B).obj Y) :=
  Equiv.ofBijective (commaHom U Y) (commaHom_bijective U Y)

omit [IsGroupoid C] [∀ A : C, (tensorRight A).Faithful] in
lemma commaHom_naturality {B : C}
    (U : CostructuredArrow (projection (D := D)) ⟨B⟩) {Y Z : D}
    (g : commaTransportObj U ⟶ Y) (k : Y ⟶ Z) :
    commaHom U Z (g ≫ k) = commaHom U Y g ≫ (commaEntry B).map k := by
  apply CostructuredArrow.hom_ext
  change ActionLocalization.mkHom ⟨(commaBaseRep U).denom,
    ((commaBaseRep U).map, g ≫ k)⟩ =
    ActionLocalization.mkHom ⟨(commaBaseRep U).denom, ((commaBaseRep U).map, g)⟩ ≫
      ActionLocalization.ofHom (X := (B, Y)) (Y := (B, Z)) (𝟙 B, k)
  rw [ActionLocalization.mkHom_comp_ofHom]
  congr 1
  simp

/-- The transport functor is left adjoint to the actual fiber entry. -/
def commaTransport (B : C) : CostructuredArrow (projection (D := D)) ⟨B⟩ ⥤ D :=
  Adjunction.leftAdjointOfEquiv (fun U Y ↦ commaHomEquiv U Y)
    (fun U _ _ g h ↦ commaHom_naturality U h g)

/-- The adjunction realizes to a homotopy equivalence with the original fiber. -/
def commaTransportAdjunction (B : C) : commaTransport (D := D) B ⊣ commaEntry B :=
  Adjunction.adjunctionOfEquivLeft _ _

end CategoryTheory.GroupCompletion.Localization
