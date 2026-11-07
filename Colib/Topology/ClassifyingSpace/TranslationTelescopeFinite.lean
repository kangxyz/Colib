/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Monoidal.TranslationTelescope
public import Colib.Topology.ClassifyingSpace.GrothendieckTelescope

/-!
Adapted from `Quillen/Topology/ClassifyingSpace/TranslationTelescopeFinite.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual original
stage arrows, finite support and coefficient corrections.
 # Actual left translation restricted to finite telescope prefixes -/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (e P : C)

/-- Restrict the original left action to a finite prefix, preserving its base arrows. -/
def prefixTranslation (n : ℕ) :
    Grothendieck.FiniteTelescope.Model (diagram e) n ⥤
      Grothendieck.FiniteTelescope.Model (diagram e) n where
  obj X :=
    { base := X.base
      fiber := ((leftTranslation e P).obj
        ((Grothendieck.Telescope.prefixInclusion (diagram e) n).obj X)).fiber }
  map f :=
    { base := f.base
      fiber := ((leftTranslation e P).map
        ((Grothendieck.Telescope.prefixInclusion (diagram e) n).map f)).fiber }
  map_id X := by
    apply (Grothendieck.Telescope.prefixInclusion (diagram e) n).map_injective
    change (leftTranslation e P).map
      ((Grothendieck.Telescope.prefixInclusion (diagram e) n).map (𝟙 X)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  map_comp f g := by
    apply (Grothendieck.Telescope.prefixInclusion (diagram e) n).map_injective
    rw [CategoryTheory.Functor.map_comp]
    change (leftTranslation e P).map
      ((Grothendieck.Telescope.prefixInclusion (diagram e) n).map (f ≫ g)) =
        (leftTranslation e P).map
          ((Grothendieck.Telescope.prefixInclusion (diagram e) n).map f) ≫
        (leftTranslation e P).map
          ((Grothendieck.Telescope.prefixInclusion (diagram e) n).map g)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]

/-- Restriction commutes exactly with the original infinite-prefix inclusion. -/
theorem prefixTranslation_inclusion (n : ℕ) :
    prefixTranslation e P n ⋙ Grothendieck.Telescope.prefixInclusion (diagram e) n =
      Grothendieck.Telescope.prefixInclusion (diagram e) n ⋙ leftTranslation e P := rfl

/-- Restriction commutes exactly with the original prefix transition. -/
theorem prefixTranslation_transition {n m : ℕ} (h : n ≤ m) :
    prefixTranslation e P n ⋙ Grothendieck.Telescope.prefixTransition (diagram e) h =
      Grothendieck.Telescope.prefixTransition (diagram e) h ⋙ prefixTranslation e P m := rfl

/-- At the last stage the restricted action is the original finite-stage left tensor functor. -/
theorem lastInclusion_prefixTranslation (n : ℕ) :
    Grothendieck.FiniteTelescope.inclusion (diagram e) n (Fin.last n) ⋙
        prefixTranslation e P n =
      (AsSmall.down ⋙ tensorLeft P ⋙ AsSmall.up) ⋙
        Grothendieck.FiniteTelescope.inclusion (diagram e) n (Fin.last n) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply (Grothendieck.Telescope.prefixInclusion (diagram e) n).map_injective
  change (leftTranslation e P).map ((Grothendieck.ι (diagram e) n).map f) =
    (Grothendieck.ι (diagram e) n).map ((AsSmall.down ⋙ tensorLeft P ⋙ AsSmall.up).map f)
  exact eq_of_heq (CategoryTheory.Functor.hcongr_hom (inclusion_leftTranslation e P n) f)

end CategoryTheory.MonoidalCategory.TranslationTelescope
