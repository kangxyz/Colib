/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.TelescopeTransitions
public import Colib.CategoryTheory.GroupCompletion.FixedFirstEntry
public import Colib.CategoryTheory.Grothendieck.FiberTransitions

/-! # Coherence of the actual localized stage transitions -/

/-!
Implementation provenance: adapted from
`Quillen/CategoryTheory/GroupCompletion/TelescopeTransitionLaws.lean` at
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

/-- The localized identity transition retains the actual diagram identity cast. -/
theorem localizationStageTransition_id (n : ℕ) :
    localizationStageTransition e (𝟙 n) =
      eqToHom (by rw [(localizationDiagram e).map_id]; rfl) := by
  apply NatTrans.ext
  funext X
  rw [localizationStageTransition_app]
  simp only [eqToHom_app]
  have h := congrArg (fun η ↦ η.app (AsSmall.up.obj X.obj.2))
    (Grothendieck.fiberTransition_id (diagram e) n)
  have hh := congrArg ((Localization.fixedFirstEntry X.obj.1).map) h
  simp only [eqToHom_app, eqToHom_map] at hh
  exact hh

/-- Composition retains precisely the original completed diagram composition cast. -/
theorem localizationStageTransition_comp {n m k : ℕ} (h : n ⟶ m) (g : m ⟶ k) :
    localizationStageTransition e (h ≫ g) =
      localizationStageTransition e h ≫
        Functor.whiskerLeft ((localizationDiagram e).map h).toFunctor
          (localizationStageTransition e g) ≫
            eqToHom (by rw [(localizationDiagram e).map_comp]; rfl) := by
  apply NatTrans.ext
  funext X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app,
    localizationStageTransition_app]
  have ht := congrArg (fun η ↦ η.app (AsSmall.up.obj X.obj.2))
    (Grothendieck.fiberTransition_comp (diagram e) h g)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app] at ht
  have hh := congrArg ((Localization.fixedFirstEntry X.obj.1).map) ht
  simp only [Functor.map_comp, eqToHom_map] at hh
  exact hh

end CategoryTheory.MonoidalCategory.TranslationTelescope
