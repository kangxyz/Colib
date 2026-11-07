/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.ActionLocalization
public import Mathlib.CategoryTheory.Monoidal.Action.LinearFunctor

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/Functoriality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Functoriality of Grayson's action category

A lax left-linear functor descends to the category associated to a monoidal
action. Invertibility of its lineator is not needed for this construction.
-/

@[expose] public section

universe u v u₁ v₁ u₂ v₂

open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open CategoryTheory.Functor.LaxLeftLinear

namespace CategoryTheory.GroupCompletion.ActionLocalization

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalLeftAction C D]
  {E : Type u₂} [Category.{v₂} E] [MonoidalLeftAction C E]
  (F : D ⥤ E) [F.LaxLeftLinear C]

/-- Apply a lax left-linear functor to a translated morphism. -/
def HomRep.mapRep {X Y : D} (f : HomRep (C := C) X Y) :
    HomRep (C := C) (F.obj X) (F.obj Y) :=
  ⟨f.denom, μₗ F f.denom X ≫ F.map f.map⟩

lemma HomRep.map_rel {X Y : D} {f g : HomRep (C := C) X Y}
    (h : Rel f g) : Rel (HomRep.mapRep F f) (HomRep.mapRep F g) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  change e.hom ⊵ₗ F.obj X ≫ μₗ F g.denom X ≫ F.map g.map =
    μₗ F f.denom X ≫ F.map f.map
  rw [μₗ_naturality_left_assoc, ← F.map_comp, he]

lemma HomRep.map_id (X : D) : HomRep.mapRep F (HomRep.id (C := C) X) = HomRep.id (F.obj X) := by
  exact congrArg (HomRep.mk (𝟙_ C)) (μₗ_unitality F X).symm

lemma HomRep.map_comp {X Y Z : D} (f : HomRep (C := C) X Y)
    (g : HomRep (C := C) Y Z) :
    HomRep.mapRep F (f.comp g) = (HomRep.mapRep F f).comp (HomRep.mapRep F g) := by
  apply congrArg (HomRep.mk (g.denom ⊗ f.denom))
  dsimp only [HomRep.mapRep, HomRep.comp]
  simp only [Functor.map_comp, Category.assoc, μₗ_associativity_assoc,
    MonoidalLeftAction.actionHomRight_comp]
  rw [μₗ_naturality_right_assoc]

/-- Descent of a lax left-linear functor to Grayson's action categories. -/
def mapFunctor : ActionLocalization C D ⥤ ActionLocalization C E where
  obj X := ⟨F.obj X.obj⟩
  map := Quotient.map (HomRep.mapRep F) (fun _ _ h ↦ HomRep.map_rel F h)
  map_id X := congrArg mkHom (HomRep.map_id F X.obj)
  map_comp := by
    rintro X Y Z ⟨f⟩ ⟨g⟩
    exact congrArg mkHom (HomRep.map_comp F f g)

@[simp]
lemma mapFunctor_mkHom {X Y : D} (f : HomRep (C := C) X Y) :
    (mapFunctor F).map (mkHom f) = mkHom (HomRep.mapRep F f) := rfl

@[simp]
lemma mapFunctor_ofHom {X Y : D} (f : X ⟶ Y) :
    (mapFunctor F).map (ofHom (C := C) f) = ofHom (C := C) (F.map f) := by
  change mkHom ⟨𝟙_ C, _⟩ = mkHom ⟨𝟙_ C, _⟩
  congr 1
  exact congrArg (HomRep.mk (𝟙_ C)) (by
    simp only [Functor.map_comp, ← Category.assoc, ← μₗ_unitality])

/-- Composition with an original morphism on the target keeps the translation. -/
lemma mkHom_comp_ofHom {X Y Z : D} (f : HomRep (C := C) X Y) (g : Y ⟶ Z) :
    mkHom f ≫ ofHom (C := C) g = mkHom ⟨f.denom, f.map ≫ g⟩ := by
  apply Quotient.sound
  refine ⟨λ_ f.denom, ?_⟩
  simp [HomRep.comp, Category.assoc]

/-- Composition with an original morphism on the source keeps the translation. -/
lemma ofHom_comp_mkHom {X Y Z : D} (f : X ⟶ Y) (g : HomRep (C := C) Y Z) :
    ofHom (C := C) f ≫ mkHom g = mkHom ⟨g.denom, g.denom ⊴ₗ f ≫ g.map⟩ := by
  apply Quotient.sound
  refine ⟨ρ_ g.denom, ?_⟩
  simp [HomRep.comp, Category.assoc]

/-- A natural transformation compatible with the lax lineators descends to
Grayson's action categories. -/
def mapNatTrans {G : D ⥤ E} [G.LaxLeftLinear C] (η : F ⟶ G)
    (hη : ∀ (s : C) (X : D),
      μₗ F s X ≫ η.app (s ⊙ₗ X) = s ⊴ₗ η.app X ≫ μₗ G s X) :
    mapFunctor (C := C) F ⟶ mapFunctor (C := C) G where
  app X := ofHom (η.app X.obj)
  naturality := by
    rintro X Y ⟨f⟩
    change mkHom (HomRep.mapRep F f) ≫ ofHom (η.app Y.obj) =
      ofHom (η.app X.obj) ≫ mkHom (HomRep.mapRep G f)
    rw [mkHom_comp_ofHom, ofHom_comp_mkHom]
    apply congrArg mkHom
    apply congrArg (HomRep.mk f.denom)
    dsimp only [HomRep.mapRep]
    rw [Category.assoc, η.naturality, ← Category.assoc, hη, Category.assoc]

@[simp]
lemma mapNatTrans_app {G : D ⥤ E} [G.LaxLeftLinear C] (η : F ⟶ G)
    (hη : ∀ (s : C) (X : D),
      μₗ F s X ≫ η.app (s ⊙ₗ X) = s ⊴ₗ η.app X ≫ μₗ G s X)
    (X : ActionLocalization C D) :
    (mapNatTrans F η hη).app X = ofHom (η.app X.obj) := rfl

end CategoryTheory.GroupCompletion.ActionLocalization
