/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.ActionLocalization
public import Mathlib.CategoryTheory.Products.Basic

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/DiagonalAction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Grayson's category for a diagonal action

A monoidal category `C` acting on `D` also acts diagonally on `C × D`.
The category `C⁻¹D` is the action category of this diagonal action. In particular,
`C⁻¹C` has pairs of objects and arrows represented by a common translating
object and two component maps, modulo compatible isomorphisms of that object.

All associators and unitors are retained. No symmetry, faithfulness of
translations, or groupoid hypothesis is needed for this categorical construction.
The subsequent group-completion theorems require additional hypotheses and
are not asserted here.
-/

@[expose] public section

universe u v u' v'

open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction

namespace CategoryTheory.GroupCompletion

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [MonoidalCategory C] [MonoidalLeftAction C D]

/-- The diagonal action uses tensor product in the first coordinate and the
given action in the second. -/
instance diagonalLeftAction : MonoidalLeftAction C (C × D) where
  actionObj c x := (c ⊗ x.1, c ⊙ₗ x.2)
  actionHomLeft f x := (f ▷ x.1, f ⊵ₗ x.2)
  actionHomRight c _ _ f := (c ◁ f.1, c ⊴ₗ f.2)
  actionHom f g := (f ⊗ₘ g.1, f ⊙ₗₘ g.2)
  actionAssocIso c c' x := (α_ c c' x.1).prod (αₗ c c' x.2)
  actionUnitIso x := (λ_ x.1).prod (λₗ[C] x.2)
  actionHom_def f g := Prod.ext
    (MonoidalCategory.tensorHom_def f g.1)
    (MonoidalLeftAction.actionHom_def f g.2)
  actionHomRight_id c x := Prod.ext
    (MonoidalCategory.whiskerLeft_id c x.1)
    (MonoidalLeftAction.actionHomRight_id c x.2)
  id_actionHomLeft c x := Prod.ext
    (MonoidalCategory.id_whiskerRight c x.1)
    (MonoidalLeftAction.id_actionHomLeft c x.2)
  actionHom_comp f₁ f₂ g₁ g₂ := Prod.ext
    (MonoidalLeftAction.actionHom_comp (D := C) f₁ f₂ g₁.1 g₂.1)
    (MonoidalLeftAction.actionHom_comp f₁ f₂ g₁.2 g₂.2)
  actionAssocIso_hom_naturality f g h := Prod.ext
    (MonoidalCategory.associator_naturality f g h.1)
    (MonoidalLeftAction.actionAssocIso_hom_naturality f g h.2)
  actionUnitIso_hom_naturality f := Prod.ext
    (MonoidalLeftAction.actionUnitIso_hom_naturality (C := C) f.1)
    (MonoidalLeftAction.actionUnitIso_hom_naturality f.2)
  whiskerLeft_actionHomLeft c _ _ f x := Prod.ext
    (MonoidalLeftAction.whiskerLeft_actionHomLeft (D := C) c f x.1)
    (MonoidalLeftAction.whiskerLeft_actionHomLeft c f x.2)
  whiskerRight_actionHomLeft c f x := Prod.ext
    (MonoidalLeftAction.whiskerRight_actionHomLeft (D := C) c f x.1)
    (MonoidalLeftAction.whiskerRight_actionHomLeft c f x.2)
  associator_actionHom c₁ c₂ c₃ x := Prod.ext
    (MonoidalLeftAction.associator_actionHom (D := C) c₁ c₂ c₃ x.1)
    (MonoidalLeftAction.associator_actionHom c₁ c₂ c₃ x.2)
  leftUnitor_actionHom c x := Prod.ext
    (MonoidalLeftAction.leftUnitor_actionHom (D := C) c x.1)
    (MonoidalLeftAction.leftUnitor_actionHom c x.2)
  rightUnitor_actionHom c x := Prod.ext
    (MonoidalLeftAction.rightUnitor_actionHom (D := C) c x.1)
    (MonoidalLeftAction.rightUnitor_actionHom c x.2)

/-- Grayson's category `C⁻¹D` is formed from the diagonal action on `C × D`.
This definition is independent of the Q-construction. -/
abbrev Localization (C : Type u) (D : Type u') := ActionLocalization C (C × D)

namespace Localization

/-- A concrete representative of an arrow of `C⁻¹D` with its common
translating object and the two original component maps. -/
def mkHom {X Y : C × D} (s : C) (f : s ⊗ X.1 ⟶ Y.1)
    (g : s ⊙ₗ X.2 ⟶ Y.2) : (⟨X⟩ : Localization C D) ⟶ ⟨Y⟩ :=
  ActionLocalization.mkHom ⟨s, (f, g)⟩

/-- Equality in `C⁻¹D` is exactly a single compatible isomorphism of the
common translating objects, simultaneously on both coordinates. -/
theorem mkHom_eq_iff {X Y : C × D} (s t : C)
    (f : s ⊗ X.1 ⟶ Y.1) (g : s ⊙ₗ X.2 ⟶ Y.2)
    (f' : t ⊗ X.1 ⟶ Y.1) (g' : t ⊙ₗ X.2 ⟶ Y.2) :
    mkHom s f g = mkHom t f' g' ↔
      ∃ e : s ≅ t, e.hom ▷ X.1 ≫ f' = f ∧ e.hom ⊵ₗ X.2 ≫ g' = g := by
  rw [mkHom, mkHom, ActionLocalization.mkHom_eq_iff]
  change (∃ e : s ≅ t,
    (e.hom ▷ X.1 ≫ f', e.hom ⊵ₗ X.2 ≫ g') = (f, g)) ↔ _
  simp only [Prod.mk.injEq]

end Localization

end CategoryTheory.GroupCompletion
