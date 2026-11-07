/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.StableGeneralLinearCharacter
public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletionStages
public import Colib.Topology.ClassifyingSpace.UniverseHomotopy
public import Colib.Topology.ClassifyingSpace.GroupHom

/-!
# The original stable completion map detected by its quotient character

Realization of the actual categorical character recovers the original stable
quotient map up to genuine homotopy, retaining the established telescope inverse.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Topology SSet HomotopyGroup CategoryTheory.Limits
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  ModuleCat.FiniteProjective.categoryDirectSumMonoidal
  ModuleCat.FiniteProjective.directSumMonoidal
  ModuleCat.FiniteProjective.directSumSymmetric
namespace ModuleCat.FiniteProjective.StableCompletion
variable (R : Type u) [Ring R]

/-- The actual completion character, realized on the original classifying spaces. -/
def quotientDetectionMap : C(ClassifyingSpace (Completion R),
    ClassifyingSpace (SingleObj (StableGeneralLinear.ElementaryQuotient R))) :=
  classifyingSpaceMapUniversal (stableCompletionCharacter R)

/-- The realized up functor is the established common-universe homeomorphism. -/
lemma stableUp_realization :
    classifyingSpaceMapUniversal
      (AsSmall.up : SingleObj (StableGeneralLinear.Group R) ⥤
        StableGeneralLinear.stableCategory R) =
    (⟨asSmallClassifyingHomeomorph
        (SingleObj (StableGeneralLinear.Group R)),
      (asSmallClassifyingHomeomorph
        (SingleObj (StableGeneralLinear.Group R))).continuous⟩ : C(_, _)) := by
  apply DFunLike.coe_injective
  apply realization_ext
  intro n x t
  rw [classifyingSpaceMapUniversal_simplex]
  change SSet.toTop.map (SSet.yonedaEquiv.symm (x ⋙ AsSmall.up))
    ((SimplexCategory.toTopHomeo n).symm t) =
      (SSet.toTop.map (SSet.yonedaEquiv.symm x) ≫
        SSet.toTop.map (asSmallNerveIso (SingleObj (StableGeneralLinear.Group R))).hom)
          ((SimplexCategory.toTopHomeo n).symm t)
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp]
  rfl

/-- The original small-model quotient followed by the canonical up map is the original group map. -/
lemma quotientCategory_realization :
    (classifyingSpaceMapUniversal (quotientCategoryFunctor R)).comp
      (classifyingSpaceMapUniversal
        (AsSmall.up : SingleObj (StableGeneralLinear.Group R) ⥤
          StableGeneralLinear.stableCategory R)) =
        (GroupoidClassifying.classifyingMap (StableGeneralLinear.quotientMap R)).hom := by
  rw [← classifyingSpaceMapUniversal_comp]
  change classifyingSpaceMapUniversal (StableGeneralLinear.quotientMap R).toFunctor = _
  exact classifyingSpaceMapUniversal_eq _

/-- The actual telescope character comparison realizes to a genuine homotopy. -/
lemma telescope_quotientDetection_homotopic :
    ((quotientDetectionMap R).comp (telescopeMap R)).Homotopic
      ((classifyingSpaceMapUniversal (quotientCategoryFunctor R)).comp
        (classifyingSpaceMap (StableGeneralLinear.GrothendieckModel.projection R)).hom) := by
  have h : (classifyingSpaceMapUniversal
      (telescopeFunctor R ⋙ stableCompletionCharacter R)).Homotopic
      (classifyingSpaceMapUniversal
        (StableGeneralLinear.GrothendieckModel.projection R ⋙ quotientCategoryFunctor R)) :=
    ⟨classifyingSpaceUniversalHomotopy (telescopeCharacterIso R).hom⟩
  simpa only [quotientDetectionMap, telescopeMap, classifyingSpaceMapUniversal_comp,
    classifyingSpaceMapUniversal_eq] using h

/-- Composing the original stable comparison with its actual quotient detector recovers
exactly the original group quotient map up to genuine homotopy. -/
theorem stableMap_quotientDetection_homotopic :
    ((quotientDetectionMap R).comp (stableMap R)).Homotopic
      (GroupoidClassifying.classifyingMap (StableGeneralLinear.quotientMap R)).hom := by
  have h₁ := (telescope_quotientDetection_homotopic R).comp
    (ContinuousMap.Homotopic.refl (originalStableToTelescope R))
  have h₂ := (ContinuousMap.Homotopic.refl
    (classifyingSpaceMapUniversal (quotientCategoryFunctor R))).comp
      (originalStableToTelescope_projection R)
  rw [← stableUp_realization R] at h₂
  rw [quotientCategory_realization R] at h₂
  exact h₁.trans (by simpa only [ContinuousMap.comp_assoc] using h₂)

end ModuleCat.FiniteProjective.StableCompletion
