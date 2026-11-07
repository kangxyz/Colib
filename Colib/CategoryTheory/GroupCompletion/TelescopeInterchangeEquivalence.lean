/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.TelescopeInterchangeMaps
public import Colib.CategoryTheory.Monoidal.TranslationTelescopeFactorization
public import Mathlib.CategoryTheory.Equivalence

/-! # Equivalence for the original localization–Grothendieck interchange -/

/-!
Implementation provenance: adapted from
`Quillen/CategoryTheory/GroupCompletion/TelescopeInterchangeEquivalence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors,
comparison maps, homotopies, hypotheses and universes are retained.
-/

@[expose] public section

open CategoryTheory.GroupCompletion

noncomputable section
open CategoryTheory MonoidalCategory Grothendieck
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
open GroupCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (e : C)
attribute [local instance] monoidalLeftAction

/-- Every actual localized telescope arrow lifts with its original denominator,
base arrow, and inverse-lineator-normalized fiber. -/
instance localizationInterchange_full : (localizationInterchange e).Full where
  map_surjective {U V} a := by
    rcases U with ⟨n, ⟨A, X⟩⟩
    rcases V with ⟨m, ⟨B, Y⟩⟩
    induction a using Quotient.inductionOn with
    | h r =>
      refine ⟨⟨r.map.2.base, Localization.mkHom r.denom r.map.1
        (rightIterateLineator e (m - n) r.denom X ≫ stageFiber e r.map.2)⟩, ?_⟩
      rw [localizationInterchange_map_mkHom]
      erw [translatedStageTransition_factorization]
      rfl

/-- The original interchange reflects quotient equality, by cancelling the
actual epic translated stage transition and reflecting its vertical stage map. -/
instance localizationInterchange_faithful : (localizationInterchange e).Faithful where
  map_injective {U V} a b w := by
    rcases U with ⟨n, ⟨A, X⟩⟩
    rcases V with ⟨m, ⟨B, Y⟩⟩
    rcases a with ⟨h, a⟩
    rcases b with ⟨k, b⟩
    obtain rfl : h = k := Subsingleton.elim _ _
    induction a using Quotient.inductionOn with
    | h r =>
      induction b using Quotient.inductionOn with
      | h t =>
        erw [localizationInterchange_map_mkHom, localizationInterchange_map_mkHom] at w
        obtain ⟨i, hi⟩ := (ActionLocalization.mkHom_eq_iff _ _).mp w
        have h₁ := congrArg _root_.Prod.fst hi
        have h₂ := congrArg _root_.Prod.snd hi
        change (leftTranslationNatTrans e i.hom).app ((stageInclusion e n).obj X) ≫
            ((leftTranslation e t.denom).map ((stageTransition e h).app X) ≫
              stageArrow e m t.map.2) =
          (leftTranslation e r.denom).map ((stageTransition e h).app X) ≫
            stageArrow e m r.map.2 at h₂
        rw [leftTranslationNatTrans_app] at h₂
        change stageArrow e n (i.hom ▷ X) ≫
            ((leftTranslation e t.denom).map ((stageTransition e h).app X) ≫
              stageArrow e m t.map.2) =
          (leftTranslation e r.denom).map ((stageTransition e h).app X) ≫
            stageArrow e m r.map.2 at h₂
        have hn := (leftTranslationNatTrans e i.hom).naturality ((stageTransition e h).app X)
        rw [leftTranslationNatTrans_app, leftTranslationNatTrans_app] at hn
        change (leftTranslation e r.denom).map ((stageTransition e h).app X) ≫
            stageArrow e m (i.hom ▷ (EndofunctorTelescope.iterate (tensorRight e) (m - n)).obj X) =
          stageArrow e n (i.hom ▷ X) ≫
            (leftTranslation e t.denom).map ((stageTransition e h).app X) at hn
        rw [← Category.assoc, ← hn, Category.assoc, ← stageArrow_comp] at h₂
        let := translatedStageTransition_epi e h r.denom X
        have hv := stageArrow_injective e m ((cancel_epi _).mp h₂)
        refine Grothendieck.ext _ _ rfl ?_
        simp only [eqToHom_refl, Category.id_comp]
        exact Quotient.sound ⟨i, Prod.ext h₁ hv⟩

/-- Every original localized telescope object retains an exact completed stage. -/
instance localizationInterchange_essSurj : (localizationInterchange e).EssSurj where
  mem_essImage X := by
    refine ⟨⟨X.obj.2.base, ⟨X.obj.1, AsSmall.down.obj X.obj.2.fiber⟩⟩, ⟨?_⟩⟩
    exact Iso.refl _

/-- Full faithfulness and essential surjectivity make the original interchange an equivalence. -/
instance localizationInterchange_isEquivalence : (localizationInterchange e).IsEquivalence where

/-- The genuine interchange equivalence retains the original completed-stage
functor in its forward direction. -/
def localizationInterchangeEquivalence :
    Grothendieck (localizationDiagram e) ≌ Localization C (Model e) :=
  (localizationInterchange e).asEquivalence

end CategoryTheory.MonoidalCategory.TranslationTelescope
