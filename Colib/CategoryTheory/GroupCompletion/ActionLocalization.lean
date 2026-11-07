/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Monoidal.Action.Basic
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/ActionLocalization.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The category associated to a monoidal action

For a monoidal category `C` acting on `D`, Grayson's category `⟨C, D⟩`
has the objects of `D`. A morphism is represented by an object `s : C`
and a morphism `s ⊙ₗ x ⟶ y`, modulo compatible isomorphisms of `s`.
Composition uses the actual action associator; no strictness assumption is made.

This is the categorical input to `C⁻¹D = ⟨C, C × D⟩`. The construction
asserts no group-completion or homological property of its realization.

## References

* Daniel Grayson, *Higher algebraic K-theory II (after Daniel Quillen)*,
  the definition of `⟨S, X⟩` and `S⁻¹X`.
-/

@[expose] public section

universe u v u' v'

open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction

namespace CategoryTheory.GroupCompletion

/-- Objects of the category associated to the action of `C` on `D`.
The wrapper separates the new morphisms from those of `D`. -/
structure ActionLocalization (C : Type u) (D : Type u') where
  /-- The underlying object of the acted-on category. -/
  obj : D

namespace ActionLocalization

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [MonoidalCategory C] [MonoidalLeftAction C D]

/-- A morphism representative consists of a translation and a map from
that translate of the source to the target. -/
structure HomRep (X Y : D) where
  /-- The translating object. -/
  denom : C
  /-- The map after translation. -/
  map : denom ⊙ₗ X ⟶ Y

namespace HomRep

variable {X Y Z W : D}

/-- Changing a translating object by a compatible isomorphism does not
change the represented morphism. -/
def Rel (f g : HomRep (C := C) X Y) : Prop :=
  ∃ e : f.denom ≅ g.denom, e.hom ⊵ₗ X ≫ g.map = f.map

lemma rel_refl (f : HomRep (C := C) X Y) : Rel f f :=
  ⟨Iso.refl _, by simp⟩

lemma rel_symm {f g : HomRep (C := C) X Y} (h : Rel f g) : Rel g f := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  rw [← he]
  simp

lemma rel_trans {f g h : HomRep (C := C) X Y}
    (hfg : Rel f g) (hgh : Rel g h) : Rel f h := by
  obtain ⟨e, he⟩ := hfg
  obtain ⟨e', he'⟩ := hgh
  exact ⟨e ≪≫ e', by simp [he, he', Category.assoc]⟩

/-- The exact equivalence relation on representatives. -/
def setoid (X Y : D) : Setoid (HomRep (C := C) X Y) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

/-- The unit translation represents the identity. -/
def id (X : D) : HomRep (C := C) X X :=
  ⟨𝟙_ C, (λₗ[C] X).hom⟩

/-- Compose representatives by translating the first map with the second
translation. The associator is retained explicitly. -/
def comp (f : HomRep (C := C) X Y) (g : HomRep (C := C) Y Z) :
    HomRep (C := C) X Z :=
  ⟨g.denom ⊗ f.denom, (αₗ g.denom f.denom X).hom ≫ g.denom ⊴ₗ f.map ≫ g.map⟩

lemma comp_rel {f f' : HomRep (C := C) X Y} {g g' : HomRep (C := C) Y Z}
    (hf : Rel f f') (hg : Rel g g') : Rel (comp f g) (comp f' g') := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨d ⊗ᵢ e, ?_⟩
  change (d.hom ⊗ₘ e.hom) ⊵ₗ X ≫
    (αₗ g'.denom f'.denom X).hom ≫ g'.denom ⊴ₗ f'.map ≫ g'.map =
      (αₗ g.denom f.denom X).hom ≫ g.denom ⊴ₗ f.map ≫ g.map
  rw [← MonoidalLeftAction.actionHom_id,
    MonoidalLeftAction.actionAssocIso_hom_naturality_assoc]
  simp only [MonoidalLeftAction.actionHom_def, MonoidalLeftAction.actionHomRight_id,
    Category.comp_id, Category.assoc]
  rw [← MonoidalLeftAction.actionHomRight_comp_assoc, he,
    ← MonoidalLeftAction.action_exchange_assoc, hd]

lemma id_comp_rel (f : HomRep (C := C) X Y) : Rel (comp (id X) f) f := by
  refine ⟨ρ_ f.denom, ?_⟩
  simp [comp, id]

lemma comp_id_rel (f : HomRep (C := C) X Y) : Rel (comp f (id Y)) f := by
  refine ⟨λ_ f.denom, ?_⟩
  simp [comp, id]

lemma assoc_rel (f : HomRep (C := C) W X) (g : HomRep (C := C) X Y)
    (h : HomRep (C := C) Y Z) : Rel (comp (comp f g) h) (comp f (comp g h)) := by
  refine ⟨(α_ h.denom g.denom f.denom).symm, ?_⟩
  simp only [comp, Iso.symm_hom, MonoidalLeftAction.tensor_actionHomRight, Category.assoc,
    Iso.inv_hom_id_assoc, MonoidalLeftAction.actionHomRight_comp]
  rw [← MonoidalLeftAction.associator_actionHom_assoc]
  simp only [MonoidalLeftAction.inv_hom_actionHomLeft_assoc]

end HomRep

/-- Grayson's action category, with isomorphism classes of actual translated
morphisms. The unitors and associator prove the category laws. -/
instance category : Category.{max u v'} (ActionLocalization C D) where
  Hom X Y := Quotient (HomRep.setoid (C := C) X.obj Y.obj)
  id X := Quotient.mk _ (HomRep.id X.obj)
  comp := Quotient.map₂ HomRep.comp (fun _ _ hf _ _ hg ↦ HomRep.comp_rel hf hg)
  id_comp := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (HomRep.id_comp_rel f)
  comp_id := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (HomRep.comp_id_rel f)
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact Quotient.sound (HomRep.assoc_rel f g h)

/-- The arrow represented by a specified translated map. -/
def mkHom {X Y : D} (f : HomRep (C := C) X Y) :
    (⟨X⟩ : ActionLocalization C D) ⟶ ⟨Y⟩ := Quotient.mk _ f

/-- Equality of represented arrows is precisely compatible isomorphism of
the translating objects. -/
theorem mkHom_eq_iff {X Y : D} (f g : HomRep (C := C) X Y) :
    mkHom f = mkHom g ↔ HomRep.Rel f g := Quotient.eq

/-- Every arrow in the action category has an actual representative. -/
theorem mkHom_surjective (X Y : D) :
    Function.Surjective (mkHom : HomRep (C := C) X Y →
      ((⟨X⟩ : ActionLocalization C D) ⟶ ⟨Y⟩)) := by
  rintro ⟨f⟩
  exact ⟨f, rfl⟩

@[simp]
theorem mkHom_id (X : D) : mkHom (HomRep.id (C := C) X) = 𝟙 (⟨X⟩ : ActionLocalization C D) :=
  rfl

@[simp]
theorem mkHom_comp {X Y Z : D} (f : HomRep (C := C) X Y)
    (g : HomRep (C := C) Y Z) : mkHom (HomRep.comp f g) = mkHom f ≫ mkHom g := rfl

/-- A map of the original category, represented using the unit translation. -/
def ofHom {X Y : D} (f : X ⟶ Y) :
    (⟨X⟩ : ActionLocalization C D) ⟶ ⟨Y⟩ :=
  mkHom ⟨𝟙_ C, (λₗ[C] X).hom ≫ f⟩

@[simp]
theorem ofHom_id (X : D) : ofHom (C := C) (𝟙 X) = 𝟙 (⟨X⟩ : ActionLocalization C D) := by
  simp only [ofHom, Category.comp_id]
  rfl

@[simp]
theorem ofHom_comp {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ofHom (C := C) (f ≫ g) = ofHom (C := C) f ≫ ofHom (C := C) g := by
  apply Eq.symm
  apply Quotient.sound
  refine ⟨λ_ (𝟙_ C), ?_⟩
  simp [HomRep.comp, Category.assoc]

/-- The canonical functor into Grayson's action category. -/
def ofFunctor : D ⥤ ActionLocalization C D where
  obj X := ⟨X⟩
  map f := ofHom f
  map_id X := ofHom_id X
  map_comp f g := ofHom_comp f g

/-- The arrow that translates an object by `s`, represented by the identity
map of the translated object. -/
def translation (s : C) (X : D) :
    (⟨X⟩ : ActionLocalization C D) ⟶ ⟨s ⊙ₗ X⟩ := mkHom ⟨s, 𝟙 _⟩

/-- A represented arrow factors as its actual translation followed by the
canonical image of its original map. -/
theorem mkHom_factorization {X Y : D} (f : HomRep (C := C) X Y) :
    mkHom f = translation f.denom X ≫ ofHom f.map := by
  apply Eq.symm
  apply Quotient.sound
  refine ⟨λ_ f.denom, ?_⟩
  simp [HomRep.comp]

/-- When the acting category is a groupoid acting on itself, its unit is
initial in the action category. This is the categorical contraction input
in Grayson's construction. -/
noncomputable def selfUnitIsInitial [IsGroupoid C] :
    Limits.IsInitial (⟨𝟙_ C⟩ : ActionLocalization C C) :=
  Limits.IsInitial.ofUniqueHom
    (fun Y ↦ mkHom ⟨Y.obj, (ρ_ Y.obj).hom⟩)
    (fun Y f ↦ by
      induction f using Quotient.inductionOn with
      | _ f =>
        apply Quotient.sound
        refine ⟨(ρ_ f.denom).symm ≪≫ asIso f.map, ?_⟩
        change ((ρ_ f.denom).inv ≫ f.map) ▷ (𝟙_ C) ≫ (ρ_ Y.obj).hom = f.map
        rw [rightUnitor_naturality]
        simp)

end ActionLocalization

end CategoryTheory.GroupCompletion
