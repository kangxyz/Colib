/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionBaseChangeIdentity

/-!
# Naturality of the original completion identity-entry comparison

## Implementation provenance

Adapted from `Quillen/KTheory/Plus/ProjectiveExtensionBaseChangeIdentityNaturality.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
  directSumMonoidal directSumSymmetric inflationDirectSumAction
  rightBaseChangeMonoidal rightBaseChangeCoreMonoidal
  identityExtensionLinear identityExtensionPairLinear
variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

/-- The comparison commutes with each actual translated identity-extension arrow. -/
theorem rightBaseChangeIdentityExtension_translated
    (P B B' : IsoCategory Rᵐᵒᵖ) (b : P ⊗ B ⟶ B') :
    (rightBaseChangeExtensionTensorIso f P ((exactStructure Rᵐᵒᵖ).identityExtension B.of)).hom ≫
      (rightBaseChangeExtension f).map
        (identityExtensionLineator Rᵐᵒᵖ P B ≫
          (exactStructure Rᵐᵒᵖ).identityExtensionFunctor.map b) ≫
      (rightBaseChangeIdentityExtensionIso f B').hom =
    (rightBaseChangeCore f).obj P ⊴ₗ (rightBaseChangeIdentityExtensionIso f B).hom ≫
      identityExtensionLineator Sᵐᵒᵖ ((rightBaseChangeCore f).obj P)
        ((rightBaseChangeCore f).obj B) ≫
      (exactStructure Sᵐᵒᵖ).identityExtensionFunctor.map
        (Functor.LaxMonoidal.μ (rightBaseChangeCore f) P B ≫ (rightBaseChangeCore f).map b) := by
  apply Subdivision.hom_ext
  · simp only [Subdivision.domainMap_comp]
    apply WideSubcategory.hom_ext
    simp only [WideSubcategory.comp_def]
    change (𝟙 _ ≫ (rightBaseChange f).map (b.iso.inv ≫ 𝟙 _)) ≫
      (rightBaseChangeTensorIso f P.of B.of).inv =
      (((Functor.LaxMonoidal.μ (rightBaseChangeCore f) P B ≫
        (rightBaseChangeCore f).map b).iso.inv ≫ 𝟙 _) ≫
          ((inv (𝟙 ((rightBaseChangeCore f).obj P))).iso.hom ▷ _ ≫ _ ◁ 𝟙 _))
    simp only [Category.id_comp, Category.comp_id, IsIso.inv_id, coreCategory_id_iso,
      Iso.refl_hom, id_whiskerRight, whiskerLeft_id, coreCategory_comp_iso, Iso.trans_inv]
    rfl
  · simp only [Grothendieck.comp_base]
    apply WideSubcategory.hom_ext
    simp only [WideSubcategory.comp_def]
    change (rightBaseChangeTensorIso f P.of B.of).hom ≫
      (rightBaseChange f).map (𝟙 _ ≫ b.iso.hom) ≫ 𝟙 _ =
      ((𝟙 _ ▷ _ ≫ _ ◁ 𝟙 _) ≫ 𝟙 _) ≫
        (Functor.LaxMonoidal.μ (rightBaseChangeCore f) P B ≫
          (rightBaseChangeCore f).map b).iso.hom
    simp only [Category.id_comp, Category.comp_id, id_whiskerRight, whiskerLeft_id,
      coreCategory_comp_iso, Iso.trans_hom]
    rfl

/-- The original identity-entry functor has its exact representative formula. -/
theorem completionIdentityEntry_mkHom {A B A' B' : IsoCategory Rᵐᵒᵖ}
    (P : IsoCategory Rᵐᵒᵖ) (a : P ⊗ A ⟶ A') (b : P ⊗ B ⟶ B') :
    (completionIdentityEntry Rᵐᵒᵖ).map
        (GroupCompletion.Localization.mkHom (X := (A, B)) (Y := (A', B')) P a b) =
      GroupCompletion.Localization.mkHom
        (X := (A, (exactStructure Rᵐᵒᵖ).identityExtension B.of))
        (Y := (A', (exactStructure Rᵐᵒᵖ).identityExtension B'.of)) P a
        (identityExtensionLineator Rᵐᵒᵖ P B ≫
          (exactStructure Rᵐᵒᵖ).identityExtensionFunctor.map b) := by
  change GroupCompletion.ActionLocalization.mkHom
    (X := (A, (exactStructure Rᵐᵒᵖ).identityExtension B.of))
    (Y := (A', (exactStructure Rᵐᵒᵖ).identityExtension B'.of))
    ⟨P, (𝟙 _ ≫ a, _)⟩ = _
  rw [Category.id_comp]
  rfl

/-- The actual identity-entry square is natural on all localized morphisms. -/
def completionIdentityBaseChangeNatIso :
    completionIdentityEntry Rᵐᵒᵖ ⋙ localizedExtensionBaseChange f ≅
      completionBaseChange f ⋙ completionIdentityEntry Sᵐᵒᵖ :=
  NatIso.ofComponents (completionIdentityBaseChangeIso f) (by
    intro X Y h
    induction h using Quotient.inductionOn with
    | _ h =>
      change GroupCompletion.ActionLocalization.mkHom _ ≫
          GroupCompletion.ActionLocalization.ofHom _ =
        GroupCompletion.ActionLocalization.ofHom _ ≫
          GroupCompletion.ActionLocalization.mkHom _
      rw [GroupCompletion.ActionLocalization.mkHom_comp_ofHom,
        GroupCompletion.ActionLocalization.ofHom_comp_mkHom]
      apply congrArg GroupCompletion.ActionLocalization.mkHom
      apply congrArg (GroupCompletion.ActionLocalization.HomRep.mk
        ((rightBaseChangeCore f).obj h.denom))
      apply Prod.ext
      · change (Functor.LaxMonoidal.μ (rightBaseChangeCore f) h.denom X.obj.1 ≫
            (rightBaseChangeCore f).map (𝟙 _ ≫ h.map.1)) ≫ 𝟙 _ =
          (rightBaseChangeCore f).obj h.denom ◁ 𝟙 _ ≫
            (𝟙 _ ≫ (Functor.LaxMonoidal.μ (rightBaseChangeCore f) h.denom X.obj.1 ≫
              (rightBaseChangeCore f).map h.map.1))
        simp only [Category.id_comp, Category.comp_id, whiskerLeft_id]
      · change
          ((rightBaseChangeExtensionTensorIso f h.denom
              ((exactStructure Rᵐᵒᵖ).identityExtension X.obj.2.of)).hom ≫
            (rightBaseChangeExtension f).map
              (identityExtensionLineator Rᵐᵒᵖ h.denom X.obj.2 ≫
                (exactStructure Rᵐᵒᵖ).identityExtensionFunctor.map h.map.2)) ≫
              (rightBaseChangeIdentityExtensionIso f Y.obj.2).hom =
          (rightBaseChangeCore f).obj h.denom ⊴ₗ
              (rightBaseChangeIdentityExtensionIso f X.obj.2).hom ≫
            (identityExtensionLineator Sᵐᵒᵖ ((rightBaseChangeCore f).obj h.denom)
                ((rightBaseChangeCore f).obj X.obj.2) ≫
              (exactStructure Sᵐᵒᵖ).identityExtensionFunctor.map
                (Functor.LaxMonoidal.μ (rightBaseChangeCore f) h.denom X.obj.2 ≫
                  (rightBaseChangeCore f).map h.map.2))
        simpa only [Category.assoc] using
          rightBaseChangeIdentityExtension_translated f h.denom X.obj.2 Y.obj.2 h.map.2)

/-- The natural comparison retains the already specified original object isomorphism. -/
theorem completionIdentityBaseChangeNatIso_hom_app (U : GroupCompletionCategory Rᵐᵒᵖ) :
    (completionIdentityBaseChangeNatIso f).hom.app U =
      (completionIdentityBaseChangeIso f U).hom := rfl

/-- Naturality preserves the original quotient-zero triangle at every completion object. -/
theorem completionIdentityBaseChangeNatIso_zero_triangle (U : GroupCompletionCategory Rᵐᵒᵖ) :
    (localizedExtensionBaseChangeProjectionIso f).hom.app ((completionIdentityEntry Rᵐᵒᵖ).obj U) ≫
      (localizedExtensionProjection Sᵐᵒᵖ).map
        ((completionIdentityBaseChangeNatIso f).hom.app U) ≫
      (completionIdentityProjectionIsoZero Sᵐᵒᵖ).hom.app ((completionBaseChange f).obj U) =
    (rightBaseChangeExact f).mapQ.map ((completionIdentityProjectionIsoZero Rᵐᵒᵖ).hom.app U) ≫
      ((exactStructure Sᵐᵒᵖ).qIsoOfIso (rightBaseChange f).mapZeroObject).hom :=
  completionIdentityBaseChangeIso_zero_triangle f U

/-- The rank-zero specialization retains both actual inverse unit comparisons. -/
theorem completionIdentityBaseChangeNatIso_zero :
    (completionIdentityBaseChangeNatIso f).hom.app (StableCompletion.stageObject R 0) ≫
      (completionIdentityEntry Sᵐᵒᵖ).map (completionBaseChangeZeroIso f).hom =
        (completionIdentityBaseChangeZeroIso f).hom := rfl

end ModuleCat.FiniteProjective
