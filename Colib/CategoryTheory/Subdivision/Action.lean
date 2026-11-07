/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Subdivision.Basic
public import Mathlib.CategoryTheory.Monoidal.Action.LinearFunctor
public import Mathlib.CategoryTheory.Groupoid

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/Subdivision/Action.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Monoidal groupoid actions on subdivision categories

A monoidal groupoid acting on `D` acts on its subdivision. An actor morphism
acts by its inverse on the reversed-domain coordinate and by itself on the
codomain coordinate. The groupoid hypothesis is essential for this formula.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v u' v'

open CategoryTheory MonoidalCategory Opposite
open scoped MonoidalLeftAction

namespace CategoryTheory.Subdivision

section Basic

variable {D : Type u'} [Category.{v'} D]

lemma hom_ext {X Y : Subdivision D} (f g : X ⟶ Y)
    (hd : domainMap f = domainMap g) (hc : f.base = g.base) : f = g := by
  refine Grothendieck.ext f g hc ?_
  apply Quiver.Hom.unop_inj
  apply Over.OverMorphism.ext
  simpa [domainMap] using hd

@[simp]
lemma domainMap_id (X : Subdivision D) : domainMap (𝟙 X) = 𝟙 X.fiber.unop.left := by
  simp [domainMap]

@[simp]
lemma domainMap_comp {X Y Z : Subdivision D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    domainMap (f ≫ g) = domainMap g ≫ domainMap f := by
  simp [domainMap, Grothendieck.comp_fiber]

/-- A factorization with arbitrary subdivision objects, without choosing presentations. -/
def homMk {X Y : Subdivision D} (h : Y.fiber.unop.left ⟶ X.fiber.unop.left)
    (k : X.base ⟶ Y.base) (w : h ≫ X.fiber.unop.hom ≫ k = Y.fiber.unop.hom) : X ⟶ Y :=
  ⟨k, (Over.homMk h w).op⟩

@[simp]
lemma homMk_domainMap {X Y : Subdivision D} (h : Y.fiber.unop.left ⟶ X.fiber.unop.left)
    (k : X.base ⟶ Y.base) (w : h ≫ X.fiber.unop.hom ≫ k = Y.fiber.unop.hom) :
    domainMap (homMk h k w) = h := rfl

@[simp]
lemma homMk_base {X Y : Subdivision D} (h : Y.fiber.unop.left ⟶ X.fiber.unop.left)
    (k : X.base ⟶ Y.base) (w : h ≫ X.fiber.unop.hom ≫ k = Y.fiber.unop.hom) :
    (homMk h k w).base = k := rfl

/-- Two endpoint isomorphisms forming a square give a subdivision isomorphism. -/
def isoMk {X Y : Subdivision D} (a : X.fiber.unop.left ≅ Y.fiber.unop.left)
    (b : X.base ≅ Y.base) (w : X.fiber.unop.hom ≫ b.hom = a.hom ≫ Y.fiber.unop.hom) :
    X ≅ Y where
  hom := homMk a.inv b.hom (by rw [w]; simp)
  inv := homMk a.hom b.inv (by rw [← Category.assoc, ← w]; simp)
  hom_inv_id := by apply hom_ext <;> simp
  inv_hom_id := by apply hom_ext <;> simp

private lemma inverse_congr {A B : D} (f g : A ⟶ B) [IsIso f] [IsIso g]
    (h : f = g) : inv f = inv g := by
  subst g
  rfl

end Basic

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsGroupoid C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- Act on the represented arrow. -/
abbrev actionObj (s : C) (X : Subdivision D) : Subdivision D :=
  of (s ⊴ₗ X.fiber.unop.hom)

/-- Act on both coordinates, reversing the actor morphism in the domain coordinate. -/
def actionMap {s t : C} (f : s ⟶ t) {X Y : Subdivision D} (g : X ⟶ Y) :
    actionObj s X ⟶ actionObj t Y :=
  homMk (inv f ⊙ₗₘ domainMap g) (f ⊙ₗₘ g.base) (by
    change (inv f ⊙ₗₘ domainMap g) ≫ s ⊴ₗ X.fiber.unop.hom ≫ (f ⊙ₗₘ g.base) =
      t ⊴ₗ Y.fiber.unop.hom
    rw [← MonoidalLeftAction.id_actionHom, ← MonoidalLeftAction.actionHom_comp,
      ← MonoidalLeftAction.actionHom_comp]
    simp [factorization g])

@[simp]
lemma actionMap_domainMap {s t : C} (f : s ⟶ t) {X Y : Subdivision D} (g : X ⟶ Y) :
    domainMap (actionMap f g) = inv f ⊙ₗₘ domainMap g := rfl

@[simp]
lemma actionMap_base {s t : C} (f : s ⟶ t) {X Y : Subdivision D} (g : X ⟶ Y) :
    (actionMap f g).base = f ⊙ₗₘ g.base := rfl

lemma actionMap_id (s : C) (X : Subdivision D) : actionMap (𝟙 s) (𝟙 X) = 𝟙 (actionObj s X) := by
  apply hom_ext <;> simp [of]

lemma actionMap_comp {s t r : C} (f : s ⟶ t) (f' : t ⟶ r)
    {X Y Z : Subdivision D} (g : X ⟶ Y) (g' : Y ⟶ Z) :
    actionMap (f ≫ f') (g ≫ g') = actionMap f g ≫ actionMap f' g' := by
  apply hom_ext <;> simp [IsIso.inv_comp]

/-- The action associator, with its inverse in the reversed-domain coordinate. -/
def actionAssociator (s t : C) (X : Subdivision D) :
    actionObj (s ⊗ t) X ≅ actionObj s (actionObj t X) :=
  isoMk (αₗ s t X.fiber.unop.left) (αₗ s t X.base) (by
    change (s ⊗ t) ⊴ₗ X.fiber.unop.hom ≫ (αₗ s t X.base).hom =
      (αₗ s t X.fiber.unop.left).hom ≫ s ⊴ₗ t ⊴ₗ X.fiber.unop.hom
    simpa only [id_tensorHom_id, MonoidalLeftAction.id_actionHom] using
      MonoidalLeftAction.actionAssocIso_hom_naturality (𝟙 s) (𝟙 t) X.fiber.unop.hom)

/-- The action unitor, with its inverse in the reversed-domain coordinate. -/
def actionUnitor (X : Subdivision D) : actionObj (𝟙_ C) X ≅ X :=
  isoMk (λₗ[C] X.fiber.unop.left) (λₗ[C] X.base)
    (MonoidalLeftAction.actionUnitIso_hom_naturality X.fiber.unop.hom).symm

instance monoidalLeftAction : MonoidalLeftAction C (Subdivision D) where
  actionObj := actionObj
  actionHomLeft f X := actionMap f (𝟙 X)
  actionHomRight s _ _ f := actionMap (𝟙 s) f
  actionHom f g := actionMap f g
  actionAssocIso := actionAssociator
  actionUnitIso := actionUnitor
  actionHom_def f g := by rw [← actionMap_comp]; simp
  actionHomRight_id := actionMap_id
  id_actionHomLeft := actionMap_id
  actionHom_comp f f' g g' := actionMap_comp f f' g g'
  actionAssocIso_hom_naturality f g h := by
    apply hom_ext
    · simpa [actionAssociator, actionObj, of, isoMk] using
        (MonoidalLeftAction.actionAssocIso_inv_naturality
          (inv f) (inv g) (domainMap h)).symm
    · exact MonoidalLeftAction.actionAssocIso_hom_naturality f g h.base
  actionUnitIso_hom_naturality f := by
    apply hom_ext <;> simp [actionUnitor, isoMk]
  whiskerLeft_actionHomLeft s _ _ f X := by
    apply hom_ext <;> simp [actionAssociator, isoMk, of]
  whiskerRight_actionHomLeft s f X := by
    apply hom_ext <;> simp [actionAssociator, isoMk, of]
  associator_actionHom s t r X := by
    apply hom_ext
    · have h := inverse_congr _ _
        (MonoidalLeftAction.associator_actionHom s t r X.fiber.unop.left)
      simp only [IsIso.inv_comp, MonoidalLeftAction.inv_actionHomLeft,
        MonoidalLeftAction.inv_actionHomRight, IsIso.Iso.inv_hom] at h
      simp only [domainMap_comp, actionMap_domainMap, domainMap_id,
        actionAssociator, isoMk, homMk_domainMap, IsIso.inv_id,
        MonoidalLeftAction.id_actionHom, MonoidalLeftAction.actionHom_id,
        IsIso.Iso.inv_hom]
      rw [Category.assoc] at h ⊢
      exact h
    · simp [actionAssociator, isoMk, of]
  leftUnitor_actionHom s X := by
    apply hom_ext
    · have h := inverse_congr _ _
        (MonoidalLeftAction.leftUnitor_actionHom s X.fiber.unop.left)
      simp only [IsIso.inv_comp, MonoidalLeftAction.inv_actionHomLeft, IsIso.Iso.inv_hom] at h
      simp only [domainMap_comp, actionMap_domainMap, domainMap_id,
        actionAssociator, actionUnitor, isoMk, homMk_domainMap,
        MonoidalLeftAction.actionHom_id, IsIso.Iso.inv_hom]
      exact h
    · simp [actionAssociator, actionUnitor, isoMk, of]
  rightUnitor_actionHom s X := by
    apply hom_ext
    · have h := inverse_congr _ _
        (MonoidalLeftAction.rightUnitor_actionHom s X.fiber.unop.left)
      simp only [IsIso.inv_comp, MonoidalLeftAction.inv_actionHomLeft,
        MonoidalLeftAction.inv_actionHomRight, IsIso.Iso.inv_hom] at h
      simpa only [actionObj, of, domainMap_comp, actionAssociator, actionUnitor, isoMk,
        homMk_domainMap,
        actionMap_domainMap, domainMap_id, MonoidalLeftAction.actionHom_id,
        IsIso.inv_id, MonoidalLeftAction.id_actionHom, IsIso.Iso.inv_hom] using h
    · simp [actionAssociator, actionUnitor, isoMk, of]

@[simp]
lemma action_domainMap {s t : C} (f : s ⟶ t) {X Y : Subdivision D} (g : X ⟶ Y) :
    domainMap (f ⊙ₗₘ g) = inv f ⊙ₗₘ domainMap g := rfl

@[simp]
lemma action_base {s t : C} (f : s ⟶ t) {X Y : Subdivision D} (g : X ⟶ Y) :
    (f ⊙ₗₘ g).base = f ⊙ₗₘ g.base := rfl

/-- The codomain projection is equivariant with identity lineators. -/
instance codomainLaxLeftLinear : (codomain (C := D)).LaxLeftLinear C where
  μₗ s X := 𝟙 (s ⊙ₗ X.base)
  μₗ_naturality_left f X := by
    change f ⊵ₗ X.base ≫ 𝟙 _ = 𝟙 _ ≫ (f ⊙ₗₘ 𝟙 X.base)
    simp
  μₗ_naturality_right s _ _ f := by
    change s ⊴ₗ f.base ≫ 𝟙 _ = 𝟙 _ ≫ (𝟙 s ⊙ₗₘ f.base)
    simp
  μₗ_associativity s t X := by
    change 𝟙 _ ≫ (αₗ s t X.base).hom =
      (αₗ s t X.base).hom ≫ s ⊴ₗ 𝟙 _ ≫ 𝟙 _
    simp
  μₗ_unitality X := by
    change (λₗ[C] X.base).hom = 𝟙 _ ≫ (λₗ[C] X.base).hom
    simp

end CategoryTheory.Subdivision
