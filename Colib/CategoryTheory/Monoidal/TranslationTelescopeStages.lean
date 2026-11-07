/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Monoidal.TranslationTelescopeAction
public import Mathlib.CategoryTheory.Monoidal.Action.LinearFunctor

/-! # Genuine linear original-stage inclusions into the translation telescope -/

/-!
Implementation provenance: adapted from `Quillen/CategoryTheory/Monoidal/TranslationTelescopeStages.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors,
comparison maps, homotopies, hypotheses and universes are retained.
-/

@[expose] public section
open CategoryTheory MonoidalCategory Grothendieck
open scoped MonoidalLeftAction
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (e : C)
attribute [local instance] monoidalLeftAction

/-- Include the original actor category at its specified actual telescope stage. -/
def stageInclusion (n : ℕ) : C ⥤ Model e :=
  AsSmall.up ⋙ Grothendieck.ι (diagram e) n

/-- Its lineator is an identity because the original stage square is literal. -/
instance stageInclusionLinear (n : ℕ) : (stageInclusion e n).LaxLeftLinear C where
  μₗ _ _ := 𝟙 _
  μₗ_naturality_left f X := by
    change (leftTranslationNatTrans e f).app ((stageInclusion e n).obj X) ≫ 𝟙 _ =
      𝟙 _ ≫ stageArrow e n (f ▷ X)
    rw [leftTranslationNatTrans_app, Category.id_comp, Category.comp_id]
    rfl
  μₗ_naturality_right P _ _ f := by
    change (leftTranslation e P).map (stageArrow e n f) ≫ 𝟙 _ =
      𝟙 _ ≫ stageArrow e n (P ◁ f)
    rw [leftTranslation_map_stageArrow, Category.id_comp, Category.comp_id]
  μₗ_associativity P Q X := by
    change 𝟙 _ ≫ stageArrow e n (α_ P Q X).hom =
      (leftTranslationTensor e P Q).hom.app ((stageInclusion e n).obj X) ≫
        (leftTranslation e P).map (𝟙 _) ≫ 𝟙 _
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id,
      Category.id_comp, leftTranslationTensor_hom_app]
    rfl
  μₗ_unitality X := by
    change (leftTranslationUnit e).hom.app ((stageInclusion e n).obj X) =
      𝟙 _ ≫ stageArrow e n (λ_ X).hom
    rw [Category.id_comp, leftTranslationUnit_hom_app]
    rfl

end CategoryTheory.MonoidalCategory.TranslationTelescope
