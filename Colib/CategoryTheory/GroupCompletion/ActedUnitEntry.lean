/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.ActedFunctoriality
public import Colib.CategoryTheory.GroupCompletion.UnitEntry

/-! # The original localization unit under actual linear functors -/

/-!
Implementation provenance: adapted from `Quillen/CategoryTheory/GroupCompletion/ActedUnitEntry.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors,
comparison maps, homotopies, hypotheses and universes are retained.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory
universe u v u' v' u'' v''
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
  {E : Type u''} [Category.{v''} E] [MonoidalLeftAction C E]
  (F : D ⥤ E) [F.LaxLeftLinear C]

/-- The actual induced localization functor retains the original unit entry exactly. -/
theorem unitEntry_actedMapFunctor :
    unitEntry (C := C) (D := D) ⋙ actedMapFunctor F =
      F ⋙ unitEntry (C := C) (D := E) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact ActionLocalization.mapFunctor_ofHom _ _

end CategoryTheory.GroupCompletion.Localization
