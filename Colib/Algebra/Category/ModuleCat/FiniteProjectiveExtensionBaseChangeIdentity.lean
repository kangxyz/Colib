/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionBaseChangeProjection
public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionBaseChange
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveZeroFiberEntry

/-!
# The actual identity-extension and zero comparison under change of rings

## Implementation provenance

Adapted from `Quillen/KTheory/Plus/ProjectiveExtensionBaseChangeIdentity.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction ZeroObject
namespace ModuleCat.FiniteProjective
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
  directSumMonoidal directSumSymmetric inflationDirectSumAction
  rightBaseChangeMonoidal rightBaseChangeCoreMonoidal
variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

/-- Mapping the original identity extension is compared by identity endpoint maps. -/
def rightBaseChangeIdentityExtensionIso (B : IsoCategory Rᵐᵒᵖ) :
    (rightBaseChangeExtension f).obj ((exactStructure Rᵐᵒᵖ).identityExtension B.of) ≅
      (exactStructure Sᵐᵒᵖ).identityExtension ((rightBaseChangeCore f).obj B).of :=
  Subdivision.isoMk (Iso.refl _) (Iso.refl _) (by
    apply WideSubcategory.hom_ext
    change (rightBaseChange f).map (𝟙 B.of) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp)

/-- The underlying quotient comparison retains the original zero-object isomorphisms. -/
def rightBaseChangeIdentityQuotientIso (B : IsoCategory Rᵐᵒᵖ) :
    ((exactStructure Sᵐᵒᵖ).extensionQuotientData
      ((rightBaseChangeExtension f).obj ((exactStructure Rᵐᵒᵖ).identityExtension B.of))).obj ≅
    ((exactStructure Sᵐᵒᵖ).extensionQuotientData
      ((exactStructure Sᵐᵒᵖ).identityExtension ((rightBaseChangeCore f).obj B).of)).obj :=
  ((rightBaseChangeExact f).extensionQuotientIso
    ((exactStructure Rᵐᵒᵖ).identityExtension B.of)).symm ≪≫
    (rightBaseChange f).mapIso ((exactStructure Rᵐᵒᵖ).identityQuotientIsoZero B.of) ≪≫
    (rightBaseChange f).mapZeroObject ≪≫
    ((exactStructure Sᵐᵒᵖ).identityQuotientIsoZero ((rightBaseChangeCore f).obj B).of).symm

/-- The identity-extension comparison is recognized in the unchanged Q category. -/
theorem rightBaseChangeIdentityExtensionIso_projection (B : IsoCategory Rᵐᵒᵖ) :
    (exactStructure Sᵐᵒᵖ).extensionProjectionQMap (rightBaseChangeIdentityExtensionIso f B).hom =
      ((exactStructure Sᵐᵒᵖ).qIsoOfIso (rightBaseChangeIdentityQuotientIso f B)).hom := by
  let : Epi (Subdivision.domainMap (rightBaseChangeIdentityExtensionIso f B).hom).hom := by
    change Epi (𝟙 ((rightBaseChange f).obj B.of))
    infer_instance
  apply (exactStructure Sᵐᵒᵖ).extensionProjectionQMap_eq_qIsoOfIso
  apply (cancel_mono
    ((exactStructure Sᵐᵒᵖ).identityQuotientIsoZero ((rightBaseChangeCore f).obj B).of).hom).1
  exact (isZero_zero (Category Sᵐᵒᵖ)).eq_of_tgt _ _

/-- The precise zero triangle is proved in original modules before entering Q. -/
theorem rightBaseChangeIdentityProjection_zero (B : IsoCategory Rᵐᵒᵖ) :
    ((exactStructure Sᵐᵒᵖ).qIsoOfIso ((rightBaseChangeExact f).extensionQuotientIso
      ((exactStructure Rᵐᵒᵖ).identityExtension B.of))).hom ≫
      (exactStructure Sᵐᵒᵖ).extensionProjectionQMap
        (rightBaseChangeIdentityExtensionIso f B).hom ≫
      ((exactStructure Sᵐᵒᵖ).identityProjectionIsoZero ((rightBaseChangeCore f).obj B).of).hom =
    (rightBaseChangeExact f).mapQ.map
      ((exactStructure Rᵐᵒᵖ).identityProjectionIsoZero B.of).hom ≫
      ((exactStructure Sᵐᵒᵖ).qIsoOfIso (rightBaseChange f).mapZeroObject).hom := by
  rw [rightBaseChangeIdentityExtensionIso_projection]
  have he : (rightBaseChangeExact f).extensionQuotientIso
      ((exactStructure Rᵐᵒᵖ).identityExtension B.of) ≪≫
      rightBaseChangeIdentityQuotientIso f B ≪≫
      (exactStructure Sᵐᵒᵖ).identityQuotientIsoZero ((rightBaseChangeCore f).obj B).of =
    (rightBaseChange f).mapIso ((exactStructure Rᵐᵒᵖ).identityQuotientIsoZero B.of) ≪≫
      (rightBaseChange f).mapZeroObject := by
    apply Iso.ext
    simp only [rightBaseChangeIdentityQuotientIso, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have h := congrArg (fun e ↦ (exactStructure Sᵐᵒᵖ).qIsoOfIso e) he
  simp only [CategoryTheory.ExactCategory.ExactStructure.qIsoOfIso_trans] at h
  have hm := (rightBaseChangeExact f).mapQ_qIsoOfIso
    ((exactStructure Rᵐᵒᵖ).identityQuotientIsoZero B.of)
  erw [← hm] at h
  exact congrArg Iso.hom h

/-- The actual localized identity-entry comparison at an arbitrary completion pair. -/
def completionIdentityBaseChangeIso (U : GroupCompletionCategory Rᵐᵒᵖ) :
    (localizedExtensionBaseChange f).obj ((completionIdentityEntry Rᵐᵒᵖ).obj U) ≅
      (completionIdentityEntry Sᵐᵒᵖ).obj ((completionBaseChange f).obj U) :=
  (GroupCompletion.ActionLocalization.ofFunctor (C := IsoCategory Sᵐᵒᵖ)
    (D := IsoCategory Sᵐᵒᵖ × (exactStructure Sᵐᵒᵖ).ExtensionTotal)).mapIso
      ((Iso.refl ((rightBaseChangeCore f).obj U.obj.1)).prod
        (rightBaseChangeIdentityExtensionIso f U.obj.2))

/-- Projection of an unchanged original pair arrow is the original extension Q arrow. -/
theorem localizedExtensionProjection_ofHom {A B : IsoCategory Rᵐᵒᵖ}
    {x y : (exactStructure Rᵐᵒᵖ).ExtensionTotal} (a : A ⟶ B) (b : x ⟶ y) :
    (localizedExtensionProjection Rᵐᵒᵖ).map
      (GroupCompletion.ActionLocalization.ofHom (C := IsoCategory Rᵐᵒᵖ)
        (X := (A, x)) (Y := (B, y)) (a, b)) =
        (exactStructure Rᵐᵒᵖ).extensionProjectionQMap b := by
  let := MonoidalLeftAction.trivial (IsoCategory Rᵐᵒᵖ)
    (QConstruction (exactStructure Rᵐᵒᵖ).deflation (exactStructure Rᵐᵒᵖ).inflation)
  let := extensionProjectionLinear Rᵐᵒᵖ
  let := extensionPairProjectionLinear Rᵐᵒᵖ
  change (GroupCompletion.ActionLocalization.TrivialAction.forgetFunctor _ _).map
    ((GroupCompletion.ActionLocalization.mapFunctor (extensionPairProjection Rᵐᵒᵖ)).map
      (GroupCompletion.ActionLocalization.ofHom
        (X := (A, x)) (Y := (B, y)) (a, b))) = _
  rw [GroupCompletion.ActionLocalization.mapFunctor_ofHom,
    GroupCompletion.ActionLocalization.TrivialAction.forgetFunctor_map_ofHom]
  rfl

/-- The actual identity-entry object comparison preserves the specified original zero triangle. -/
theorem completionIdentityBaseChangeIso_zero_triangle (U : GroupCompletionCategory Rᵐᵒᵖ) :
    (localizedExtensionBaseChangeProjectionIso f).hom.app ((completionIdentityEntry Rᵐᵒᵖ).obj U) ≫
      (localizedExtensionProjection Sᵐᵒᵖ).map (completionIdentityBaseChangeIso f U).hom ≫
      (completionIdentityProjectionIsoZero Sᵐᵒᵖ).hom.app ((completionBaseChange f).obj U) =
    (rightBaseChangeExact f).mapQ.map ((completionIdentityProjectionIsoZero Rᵐᵒᵖ).hom.app U) ≫
      ((exactStructure Sᵐᵒᵖ).qIsoOfIso (rightBaseChange f).mapZeroObject).hom := by
  have hp : (localizedExtensionProjection Sᵐᵒᵖ).map
      (completionIdentityBaseChangeIso f U).hom =
      (exactStructure Sᵐᵒᵖ).extensionProjectionQMap
        (rightBaseChangeIdentityExtensionIso f U.obj.2).hom :=
    localizedExtensionProjection_ofHom (𝟙 ((rightBaseChangeCore f).obj U.obj.1))
      (rightBaseChangeIdentityExtensionIso f U.obj.2).hom
  rw [hp]
  exact rightBaseChangeIdentityProjection_zero f U.obj.2

/-- At rank zero the comparison also includes the original two inverse unit comparisons. -/
def completionIdentityBaseChangeZeroIso :
    (localizedExtensionBaseChange f).obj
      ((completionIdentityEntry Rᵐᵒᵖ).obj (StableCompletion.stageObject R 0)) ≅
    (completionIdentityEntry Sᵐᵒᵖ).obj (StableCompletion.stageObject S 0) :=
  completionIdentityBaseChangeIso f (StableCompletion.stageObject R 0) ≪≫
    (completionIdentityEntry Sᵐᵒᵖ).mapIso (completionBaseChangeZeroIso f)

/-- The rank-zero triangle retains the actual unit-comparison edge. -/
theorem completionIdentityBaseChangeZeroIso_triangle :
    (localizedExtensionBaseChangeProjectionIso f).hom.app
        ((completionIdentityEntry Rᵐᵒᵖ).obj (StableCompletion.stageObject R 0)) ≫
      (localizedExtensionProjection Sᵐᵒᵖ).map (completionIdentityBaseChangeZeroIso f).hom ≫
      (completionIdentityProjectionIsoZero Sᵐᵒᵖ).hom.app (StableCompletion.stageObject S 0) =
    (rightBaseChangeExact f).mapQ.map
        ((completionIdentityProjectionIsoZero Rᵐᵒᵖ).hom.app (StableCompletion.stageObject R 0)) ≫
      ((exactStructure Sᵐᵒᵖ).qIsoOfIso (rightBaseChange f).mapZeroObject).hom := by
  have hn := (completionIdentityProjectionIsoZero Sᵐᵒᵖ).hom.naturality
    (completionBaseChangeZeroIso f).hom
  simp only [Functor.comp_map, Functor.const_obj_map] at hn
  dsimp only [completionIdentityBaseChangeZeroIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Functor.map_comp, Category.assoc, hn]
  erw [Category.comp_id]
  exact completionIdentityBaseChangeIso_zero_triangle f (StableCompletion.stageObject R 0)

end ModuleCat.FiniteProjective
