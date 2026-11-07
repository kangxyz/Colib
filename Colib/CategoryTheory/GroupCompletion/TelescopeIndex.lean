/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.TelescopeStages

/-! # The actual stage index on localization of the original telescope

Every original left translation preserves the stage. Consequently a localized
arrow has a well-defined monotone stage arrow, recovered from any representative.
This is the index used in the localization–Grothendieck interchange.
-/

/-!
Implementation provenance: adapted from
`Quillen/CategoryTheory/GroupCompletion/TelescopeIndex.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors,
comparison maps, homotopies, hypotheses and universes are retained.
-/

@[expose] public section

open CategoryTheory.GroupCompletion

open CategoryTheory MonoidalCategory Grothendieck
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
open GroupCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (e : C)
attribute [local instance] monoidalLeftAction

/-- Recover the genuine stage arrow from a localized morphism. Quotient
compatibility uses only thinness of the ordered stage category. -/
def localizationIndex : Localization C (Model e) ⥤ ℕ where
  obj X := X.obj.2.base
  map f := Quotient.lift (fun r ↦ r.map.2.base)
    (fun _ _ _ ↦ Subsingleton.elim _ _) f
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The quotient index is exactly the original telescope index of the acted-on map. -/
theorem localizationIndex_mkHom {X Y : C × Model e} (r : C)
    (f : r ⊗ X.1 ⟶ Y.1) (g : (leftTranslation e r).obj X.2 ⟶ Y.2) :
    (localizationIndex e).map (Localization.mkHom r f g) = g.base := rfl

/-- Every completed-stage inclusion has its original constant index. -/
theorem localizationStage_index (n : ℕ) :
    localizationStage e n ⋙ localizationIndex e =
      (Functor.const (Localization C C)).obj n := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  exact Subsingleton.elim _ _

end CategoryTheory.MonoidalCategory.TranslationTelescope
