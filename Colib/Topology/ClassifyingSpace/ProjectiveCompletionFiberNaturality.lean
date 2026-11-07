/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionBaseChangeNullhomotopy
public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionFiberFormula
public import Colib.CategoryTheory.TheoremB.NaturalTransformationFiberCancellation
public import Colib.Topology.HomotopyFiber.BasedHomotopySquareMap

/-!
# The actual whole-space completion and original Q fiber square

## Implementation provenance

Adapted from `Quillen/KTheory/Plus/ProjectiveCompletionFiberNaturality.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section
noncomputable section
open Topology SSet HomotopyGroup
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace ModuleCat.FiniteProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal
variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

/-- The exact original normalized Q square on classifying spaces. -/
def completionNormalizedProjectionHomotopy :
    ((classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom.comp
      (classifyingSpaceMapUniversal (localizedExtensionProjection Rᵐᵒᵖ))).Homotopy
    ((classifyingSpaceMapUniversal (localizedExtensionProjection Sᵐᵒᵖ)).comp
      (classifyingSpaceMapUniversal (localizedExtensionBaseChange f))) :=
  (classifyingSpaceNaturalTransformationHomotopy
    (localizedExtensionBaseChangeNormalizedIso f).hom).cast
      (by rw [classifyingSpaceMap_comp, TopCat.hom_comp,
        classifyingSpaceMapUniversal_eq])
      (by rw [classifyingSpaceMap_comp, TopCat.hom_comp,
        classifyingSpaceMapUniversal_eq, classifyingSpaceMapUniversal_eq])

/-- The original normalized Q map fixes the specified original zero vertex. -/
theorem completionNormalizedQ_basepoint :
    classifyingSpaceMap (rightBaseChangeExact f).normalizedQ
      (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero) =
        classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero := by
  rw [classifyingSpaceMap_point, rightBaseChangeNormalizedZero]

/-- The actual fiber map of the normalized projection square, with original zero target. -/
def completionNormalizedFiberMap :
    C(HomotopyFiber (classifyingSpaceMapUniversal (localizedExtensionProjection Rᵐᵒᵖ))
      (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero),
      HomotopyFiber (classifyingSpaceMapUniversal (localizedExtensionProjection Sᵐᵒᵖ))
        (classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero)) :=
  HomotopyFiber.basedHomotopySquareMap
    (classifyingSpaceMapUniversal (localizedExtensionBaseChange f))
    (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
    (completionNormalizedProjectionHomotopy f) _ _ (completionNormalizedQ_basepoint f)

/-- The original normalized fiber map retains the actual total-space map. -/
theorem completionNormalizedFiberMap_source
    (z : HomotopyFiber (classifyingSpaceMapUniversal (localizedExtensionProjection Rᵐᵒᵖ))
      (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero)) :
    (completionNormalizedFiberMap f z).val.1 =
      classifyingSpaceMapUniversal (localizedExtensionBaseChange f) z.val.1 := rfl

/-- The direct source lift under the actual square is precisely the cancellation lift. -/
theorem completionNormalizedFiberMap_directLift :
    (completionNormalizedFiberMap f).comp
      (HomotopyFiber.lift (classifyingSpaceMapUniversal (localizedExtensionProjection Rᵐᵒᵖ))
        (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero)
        (classifyingSpaceMapUniversal (completionIdentityEntry Rᵐᵒᵖ))
        (completionDirectNullhomotopy Rᵐᵒᵖ)) =
    (HomotopyFiber.mapEqMap
      (classifyingSpaceMapUniversal_eq (localizedExtensionProjection Sᵐᵒᵖ)).symm
      (classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero)).comp
    (HomotopyFiber.lift (classifyingSpaceMap (localizedExtensionProjection Sᵐᵒᵖ)).hom
      (classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero)
      (classifyingSpaceMap (completionIdentityEntry Rᵐᵒᵖ ⋙ localizedExtensionBaseChange f)).hom
      (TheoremB.naturalTransformationCancellationNullhomotopy _ _ _
        (Functor.whiskerLeft (completionIdentityEntry Rᵐᵒᵖ)
          (localizedExtensionBaseChangeNormalizedIso f).hom)
        (completionBaseChangeTargetTransformation f))) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · change classifyingSpaceMapUniversal (localizedExtensionBaseChange f)
      (classifyingSpaceMapUniversal (completionIdentityEntry Rᵐᵒᵖ) x) =
      classifyingSpaceMap (completionIdentityEntry Rᵐᵒᵖ ⋙ localizedExtensionBaseChange f) x
    rw [classifyingSpaceMapUniversal_eq, classifyingSpaceMapUniversal_eq,
      classifyingSpaceMap_comp]
    rfl
  · apply ContinuousMap.ext
    intro t
    change (((completionNormalizedProjectionHomotopy f).evalAt
      (classifyingSpaceMapUniversal (completionIdentityEntry Rᵐᵒᵖ) x)).symm.trans
      ((HomotopyFiber.toPath _ _ (HomotopyFiber.lift _ _ _
        (completionDirectNullhomotopy Rᵐᵒᵖ) x)).map
          (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom.continuous)) t = _
    rw [Path.trans_apply]
    change _ = ((classifyingSpaceNaturalTransformationHomotopy
      (Functor.whiskerLeft (completionIdentityEntry Rᵐᵒᵖ)
        (localizedExtensionBaseChangeNormalizedIso f).hom)).symm.trans
      (classifyingSpaceNaturalTransformationHomotopy
        (Functor.whiskerLeft (completionIdentityEntry Rᵐᵒᵖ)
          (localizedExtensionBaseChangeNormalizedIso f).hom ≫
            completionBaseChangeTargetTransformation f))) (t, x)
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · change classifyingSpaceNaturalTransformationHomotopy _
        (_, classifyingSpaceMapUniversal (completionIdentityEntry Rᵐᵒᵖ) x) = _
      simp only [classifyingSpaceMapUniversal_eq, ContinuousMap.Homotopy.symm_apply,
        classifyingSpaceNaturalTransformationHomotopy_whiskerLeft]
    · rw [completionBaseChangeNullhomotopy_apply]
      change _ = classifyingSpaceMap (rightBaseChangeExact f).normalizedQ
        (classifyingSpaceNaturalTransformationHomotopy
          (completionIdentityProjectionIsoZero Rᵐᵒᵖ).hom (_, x))
      rw [← classifyingSpaceUniversalHomotopy_eq]
      rfl

/-- The direct original quotient lifts commute up to the genuine categorical triangle. -/
def completionDirectFiberNaturality :
    ((completionNormalizedFiberMap f).comp
      (HomotopyFiber.lift (classifyingSpaceMapUniversal (localizedExtensionProjection Rᵐᵒᵖ))
        (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero)
        (classifyingSpaceMapUniversal (completionIdentityEntry Rᵐᵒᵖ))
        (completionDirectNullhomotopy Rᵐᵒᵖ))).Homotopy
    ((HomotopyFiber.lift (classifyingSpaceMapUniversal (localizedExtensionProjection Sᵐᵒᵖ))
      (classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero)
      (classifyingSpaceMapUniversal (completionIdentityEntry Sᵐᵒᵖ))
      (completionDirectNullhomotopy Sᵐᵒᵖ)).comp (completionBaseChangeMap f)) := by
  let Hc := TheoremB.naturalTransformationFiberCancellationHomotopy
    (completionIdentityEntry Rᵐᵒᵖ ⋙ localizedExtensionBaseChange f)
    (localizedExtensionProjection Sᵐᵒᵖ) (exactStructure Sᵐᵒᵖ).qZero
    (Functor.whiskerLeft (completionIdentityEntry Rᵐᵒᵖ)
      (localizedExtensionBaseChangeNormalizedIso f).hom)
    (completionBaseChangeTargetTransformation f)
  let Hm := TheoremB.naturalTransformationFiberHomotopy
    (completionIdentityBaseChangeNatIso f).hom
    (localizedExtensionProjection Sᵐᵒᵖ) (exactStructure Sᵐᵒᵖ).qZero
    (Functor.whiskerLeft (completionBaseChange f)
      (completionIdentityProjectionIsoZero Sᵐᵒᵖ).hom)
  let J := HomotopyFiber.mapEqMap
    (classifyingSpaceMapUniversal_eq (localizedExtensionProjection Sᵐᵒᵖ)).symm
    (classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero)
  refine ((ContinuousMap.Homotopy.refl J).comp (Hc.trans Hm)).cast
    (completionNormalizedFiberMap_directLift f).symm ?_
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · change classifyingSpaceMap (completionBaseChange f ⋙ completionIdentityEntry Sᵐᵒᵖ) x =
      classifyingSpaceMapUniversal (completionIdentityEntry Sᵐᵒᵖ) (completionBaseChangeMap f x)
    simp only [classifyingSpaceMap_comp, TopCat.comp_app, completionBaseChangeMap,
      classifyingSpaceMapUniversal_eq]
    rfl
  · apply ContinuousMap.ext
    intro t
    change classifyingSpaceNaturalTransformationHomotopy
      (Functor.whiskerLeft (completionBaseChange f)
        (completionIdentityProjectionIsoZero Sᵐᵒᵖ).hom) (t, x) =
      classifyingSpaceUniversalHomotopy
        (completionIdentityProjectionIsoZero Sᵐᵒᵖ).hom (t, completionBaseChangeMap f x)
    simp only [classifyingSpaceNaturalTransformationHomotopy_whiskerLeft,
      classifyingSpaceUniversalHomotopy_eq, completionBaseChangeMap,
      classifyingSpaceMapUniversal_eq]
    rfl

/-- The original all-points structured comparison commutes with actual ring base change. -/
def completionFiberNaturality :
    ((completionNormalizedFiberMap f).comp
      (completionToOriginalQHomotopyFiber Rᵐᵒᵖ)).Homotopy
    ((completionToOriginalQHomotopyFiber Sᵐᵒᵖ).comp (completionBaseChangeMap f)) :=
  ((ContinuousMap.Homotopy.refl (completionNormalizedFiberMap f)).comp
    (completionDirectInverseLiftHomotopy Rᵐᵒᵖ).symm).trans
    ((completionDirectFiberNaturality f).trans
      ((completionDirectInverseLiftHomotopy Sᵐᵒᵖ).compContinuousMap
        (completionBaseChangeMap f)))

end ModuleCat.FiniteProjective
