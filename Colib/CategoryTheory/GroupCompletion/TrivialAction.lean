/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.ActionLocalization
public import Colib.CategoryTheory.Monoidal.TrivialAction

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/TrivialAction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Forgetting the translation for a trivial action

For the named trivial monoidal action of `C` on `D`, the underlying map of a
representative is unchanged by the defining relation of the action category.
`ActionLocalization.TrivialAction.forgetFunctor C D` therefore sends `[s, f]`
to `f`. It preserves identities and composition by the actual unit and
associativity data of the trivial action.

The relation still retains the isomorphism class of `s`. In particular, this
functor does not assert that the action category is equivalent to `D`.
-/

@[expose] public section

universe u v u' v'

open CategoryTheory MonoidalCategory

namespace CategoryTheory.GroupCompletion.ActionLocalization.TrivialAction

variable (C : Type u) (D : Type u') [Category.{v} C] [Category.{v'} D]
  [MonoidalCategory C]

attribute [local instance] MonoidalLeftAction.trivial

variable {C D}

/-- Under the trivial action, the quotient relation requires both isomorphic
translations and equal underlying maps. -/
theorem rel_iff {X Y : D} (f g : HomRep (C := C) X Y) :
    HomRep.Rel f g ↔ Nonempty (f.denom ≅ g.denom) ∧ f.map = g.map := by
  constructor
  · rintro ⟨e, he⟩
    change 𝟙 X ≫ g.map = f.map at he
    exact ⟨⟨e⟩, he.symm.trans (Category.id_comp g.map)⟩
  · rintro ⟨⟨e⟩, h⟩
    refine ⟨e, ?_⟩
    change 𝟙 X ≫ g.map = f.map
    simpa only [Category.id_comp] using h.symm

/-- The underlying map respects the actual relation defining the action
category, so it descends to its quotient morphisms. -/
theorem map_eq_of_rel {X Y : D} {f g : HomRep (C := C) X Y}
    (h : HomRep.Rel f g) : f.map = g.map := (rel_iff f g).mp h |>.2

variable (C D)

/-- Forget the translating object for the trivial monoidal action. -/
def forgetFunctor : ActionLocalization C D ⥤ D where
  obj X := X.obj
  map := Quotient.lift (fun f ↦ f.map) (fun _ _ h ↦ map_eq_of_rel h)
  map_id _ := rfl
  map_comp := by
    rintro X Y Z ⟨f⟩ ⟨g⟩
    change 𝟙 _ ≫ f.map ≫ g.map = f.map ≫ g.map
    simp

@[simp]
theorem forgetFunctor_obj (X : ActionLocalization C D) :
    (forgetFunctor C D).obj X = X.obj := rfl

variable {C D}

@[simp]
theorem forgetFunctor_map_mkHom {X Y : D} (f : HomRep (C := C) X Y) :
    (forgetFunctor C D).map (mkHom f) = f.map := rfl

@[simp]
theorem forgetFunctor_map_ofHom {X Y : D} (f : X ⟶ Y) :
    (forgetFunctor C D).map (ofHom (C := C) f) = f := by
  change 𝟙 X ≫ f = f
  simp

@[simp]
theorem forgetFunctor_map_translation (s : C) (X : D) :
    (forgetFunctor C D).map (translation s X) = 𝟙 X := rfl

variable (C D)

/-- The canonical inclusion of `D` followed by forgetting the translation is
naturally isomorphic to its identity functor. This only gives a retraction. -/
def ofFunctorCompForgetFunctorIso :
    ofFunctor (C := C) (D := D) ⋙ forgetFunctor C D ≅ 𝟭 D :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    change (forgetFunctor C D).map (ofHom f) ≫ 𝟙 Y = 𝟙 X ≫ f
    simp)

end CategoryTheory.GroupCompletion.ActionLocalization.TrivialAction
