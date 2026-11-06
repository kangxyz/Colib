/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.Naturality
public import Colib.CategoryTheory.TheoremA.Classifying

/-!
# Identifying the comma comparison through the categorical resolution

The comma category is included in the actual strict fiber of the resolved
map. Its canonical homotopy-fiber comparison agrees, including path data,
with the comparison obtained from the resolution's structure-arrow homotopy.
-/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/Resolution.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, paths and identity
basepoints are retained under native namespace and dependency ownership. -/
@[expose] public section

noncomputable section

open SSet TopCat Topology CategoryTheory
open scoped Topology unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.TheoremB

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- Realization of the categorical fiber inclusion lies strictly over the
chosen object vertex. -/
theorem resolutionInclusion_target (d : D)
    (x : ClassifyingSpace (CostructuredArrow F d)) :
    classifyingSpaceMap (TheoremA.targetProjection F)
      (classifyingSpaceMap (TheoremA.fiberInclusion F d) x) = classifyingSpacePoint d := by
  change (classifyingSpaceMap (TheoremA.fiberInclusion F d) ≫
    classifyingSpaceMap (TheoremA.targetProjection F)) x = _
  rw [← classifyingSpaceMap_comp, TheoremA.fiberInclusion_target,
    classifyingSpaceMap_const_direct]
  rfl

/-- The strict-fiber inclusion into the actual homotopy fiber of the resolved
map, using constant paths at the chosen object vertex. -/
def resolutionStrictFiberComparison (d : D) :
    C(ClassifyingSpace (CostructuredArrow F d),
      HomotopyFiber (classifyingSpaceMap (TheoremA.targetProjection F)).hom
        (classifyingSpacePoint d)) where
  toFun x := HomotopyFiber.basepoint _ _
    (classifyingSpaceMap (TheoremA.fiberInclusion F d) x) (resolutionInclusion_target F d x)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (classifyingSpaceMap (TheoremA.fiberInclusion F d)).hom.continuous.prodMk continuous_const

@[simp]
theorem resolutionStrictFiberComparison_projection (d : D) :
    (HomotopyFiber.projection (classifyingSpaceMap (TheoremA.targetProjection F)).hom
      (classifyingSpacePoint d)).comp (resolutionStrictFiberComparison F d) =
        (classifyingSpaceMap (TheoremA.fiberInclusion F d)).hom := rfl

/-- Restricting the actual resolution homotopy to a comma fiber gives exactly
the canonical comma nullhomotopy. -/
theorem comparisonClassifyingHomotopy_restrict (d : D) (t : unitInterval)
    (x : ClassifyingSpace (CostructuredArrow F d)) :
    TheoremA.comparisonClassifyingHomotopy F
      (t, classifyingSpaceMap (TheoremA.fiberInclusion F d) x) =
      commaNullhomotopy F d (t, x) := by
  change classifyingSpaceNaturalTransformationHomotopy (TheoremA.comparison F)
    (t, classifyingSpaceMap (TheoremA.fiberInclusion F d) x) =
      classifyingSpaceNaturalTransformationHomotopy (commaTransformation F d) (t, x)
  rw [← classifyingSpaceNaturalTransformationHomotopy_whiskerLeft]
  rfl

/-- The resolved source composite `|N F| ∘ |N sourceProjection|`. -/
def resolutionSourceMap :
    C(ClassifyingSpace (TheoremA.Resolution F), ClassifyingSpace D) :=
  (classifyingSpaceMap F).hom.comp (classifyingSpaceMap (TheoremA.sourceProjection F)).hom

/-- The same canonical comma comparison, lifted first over the resolution. -/
def resolutionSourceFiberComparison (d : D) :
    C(ClassifyingSpace (CostructuredArrow F d),
      HomotopyFiber (resolutionSourceMap F) (classifyingSpacePoint d)) :=
  HomotopyFiber.lift _ _ (classifyingSpaceMap (TheoremA.fiberInclusion F d)).hom
    ((commaNullhomotopy F d).cast (by
      apply ContinuousMap.ext
      intro x
      change classifyingSpaceMap F (classifyingSpaceMap (CostructuredArrow.proj F d) x) =
        classifyingSpaceMap F (classifyingSpaceMap (TheoremA.sourceProjection F)
          (classifyingSpaceMap (TheoremA.fiberInclusion F d) x))
      congr 1
      change _ = (classifyingSpaceMap (TheoremA.fiberInclusion F d) ≫
        classifyingSpaceMap (TheoremA.sourceProjection F)) x
      rw [← classifyingSpaceMap_comp, TheoremA.fiberInclusion_source]) rfl)

/-- The source projection induces the canonical map of path-space fibers. -/
def resolutionSourceFiberMap (d : D) :
    C(HomotopyFiber (resolutionSourceMap F) (classifyingSpacePoint d),
      HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d)) :=
  HomotopyFiber.map (f₁ := resolutionSourceMap F) (f₂ := (classifyingSpaceMap F).hom)
    (classifyingSpaceMap (TheoremA.sourceProjection F)).hom
    (ContinuousMap.id (ClassifyingSpace D)) rfl _

/-- The resolution recovers the prescribed comma-to-fiber map exactly. -/
theorem resolutionSourceFiberMap_comparison (d : D) :
    (resolutionSourceFiberMap F d).comp (resolutionSourceFiberComparison F d) =
      fiberComparison F d := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · change (classifyingSpaceMap (TheoremA.fiberInclusion F d) ≫
      classifyingSpaceMap (TheoremA.sourceProjection F)) x = _
    rw [← classifyingSpaceMap_comp, TheoremA.fiberInclusion_source]
    rfl
  · rfl

end CategoryTheory.TheoremB
