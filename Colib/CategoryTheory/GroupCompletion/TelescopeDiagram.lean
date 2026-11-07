/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.TelescopeIteration

/-! # The original completed telescope, exposing its actual iterated lineators -/

/-!
Implementation provenance: adapted from `Quillen/CategoryTheory/GroupCompletion/TelescopeDiagram.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors,
comparison maps, homotopies, hypotheses and universes are retained.
-/

@[expose] public section

open CategoryTheory.GroupCompletion

open CategoryTheory MonoidalCategory Grothendieck
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open GroupCompletion
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (e : C)

/-- The completed diagram uses the actual localized right iterates. -/
def localizationDiagram : ℕ ⥤ Cat.{max u v, u} where
  obj _ := Cat.of (Localization C C)
  map {n m} _ := (localizationIteration e (m - n)).toCatHom
  map_id n := by
    rw [Nat.sub_self, localizationIteration_zero]
    rfl
  map_comp {n m k} h g := by
    change (localizationIteration e (k - n)).toCatHom =
      (localizationIteration e (m - n) ⋙ localizationIteration e (k - m)).toCatHom
    rw [localizationIteration_eq, localizationIteration_eq, localizationIteration_eq]
    exact (EndofunctorTelescope.diagram (Localization.secondTranslation e)).map_comp h g

/-- This is literally the original endofunctor telescope diagram, not a replacement
with unspecified transition maps. -/
theorem localizationDiagram_eq :
    localizationDiagram e = EndofunctorTelescope.diagram (Localization.secondTranslation e) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro n m h
  exact congrArg Functor.toCatHom (localizationIteration_eq e (m - n))

end CategoryTheory.MonoidalCategory.TranslationTelescope
