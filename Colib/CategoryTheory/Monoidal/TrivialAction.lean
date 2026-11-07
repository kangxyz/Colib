/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Monoidal.Action.Basic

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/Monoidal/TrivialAction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The trivial action of a monoidal category

`MonoidalLeftAction.trivial C D` is the monoidal left action which ignores `C`:
every acting object induces the identity functor of `D`, every acting morphism
induces an identity, and the action associators and unitors are identity
isomorphisms. It is a named definition rather than a global instance, so it does
not compete with other actions on `D`.
-/

@[expose] public section

universe u v u' v'

namespace CategoryTheory.MonoidalCategory.MonoidalLeftAction

variable (C : Type u) (D : Type u') [Category.{v} C] [Category.{v'} D]
  [MonoidalCategory C]

/-- The trivial monoidal action, with every acting object inducing the identity
functor. Install this definition locally when the trivial action is intended. -/
@[instance_reducible]
def trivial : MonoidalLeftAction C D where
  actionObj _ X := X
  actionHomLeft _ X := 𝟙 X
  actionHomRight _ _ _ f := f
  actionHom _ f := f
  actionAssocIso _ _ X := Iso.refl X
  actionUnitIso X := Iso.refl X
  actionHom_def _ _ := by simp
  actionAssocIso_hom_naturality _ _ _ := by simp
  actionUnitIso_hom_naturality _ := by simp
  whiskerLeft_actionHomLeft _ _ _ _ _ := by simp
  whiskerRight_actionHomLeft _ _ _ := by simp
  associator_actionHom _ _ _ _ := by simp
  leftUnitor_actionHom _ _ := by simp
  rightUnitor_actionHom _ _ := by simp

end CategoryTheory.MonoidalCategory.MonoidalLeftAction
