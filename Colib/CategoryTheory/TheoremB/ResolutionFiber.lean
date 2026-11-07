/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.Resolution
public import Colib.Topology.HomotopyFiber.SourceEquivalence

/-!
# The resolved and original homotopy fibers are genuinely equivalent

The resolution's source projection is an actual homotopy equivalence. Its
structure-arrow homotopy and path-space homotopy invariance give an explicit
equivalence from the resolved target fiber to the fiber of `|N F|`.
We identify the comma comparison under this equivalence up to an actual
continuous homotopy, obtained by removing a constant terminal path segment.
-/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/ResolutionFiber.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, paths and identity
basepoints are retained under native namespace and dependency ownership. -/
@[expose] public section

noncomputable section

open SSet TopCat Topology CategoryTheory
open scoped Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.TheoremB

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The actual fiber of the resolved target projection is homotopy equivalent
to the fiber of the original classifying-space map. -/
def resolutionFiberEquiv (d : D) :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (classifyingSpaceMap (TheoremA.targetProjection F)).hom
        (classifyingSpacePoint d))
      (HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d)) :=
  HomotopyFiber.sourceEquivOfHomotopy (classifyingSpaceMap F).hom
    (classifyingSpaceMap (TheoremA.targetProjection F)).hom
    (TheoremA.sourceClassifyingHomotopyEquiv F)
    (TheoremA.comparisonClassifyingHomotopy F).symm (classifyingSpacePoint d)

/-- The fiber equivalence projects to the source projection of the resolution. -/
@[simp]
theorem resolutionFiberEquiv_projection (d : D) :
    (HomotopyFiber.projection (classifyingSpaceMap F).hom (classifyingSpacePoint d)).comp
      (resolutionFiberEquiv F d).toFun =
      (classifyingSpaceMap (TheoremA.sourceProjection F)).hom.comp
        (HomotopyFiber.projection (classifyingSpaceMap (TheoremA.targetProjection F)).hom
          (classifyingSpacePoint d)) := rfl

/-- The strict comma fiber included into the resolved fiber and then carried
to the original fiber by the explicit equivalence. -/
def transferredResolutionComparison (d : D) :
    C(ClassifyingSpace (CostructuredArrow F d),
      HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d)) :=
  (resolutionFiberEquiv F d).toFun.comp (resolutionStrictFiberComparison F d)

/-- Removing the constant terminal segment identifies the transferred strict
fiber inclusion with the canonical comma-to-homotopy-fiber comparison. -/
def resolutionComparisonHomotopy (d : D) :
    (transferredResolutionComparison F d).Homotopy (fiberComparison F d) where
  toFun z := ⟨((fiberComparison F d z.2).1.1,
    (Path.delayReflRight z.1 (HomotopyFiber.toPath _ _ (fiberComparison F d z.2))).toContinuousMap),
    Path.source _, Path.target _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact (HomotopyFiber.projection _ _).continuous.comp
        ((fiberComparison F d).continuous.comp continuous_snd)
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (I × ClassifyingSpace (CostructuredArrow F d)) × I =>
        commaNullhomotopy F d (qRight (z.2, z.1.1), z.1.2))
      fun_prop
  map_zero_left x := by
    apply Subtype.ext
    apply Prod.ext
    · change classifyingSpaceMap (CostructuredArrow.proj F d) x =
        (classifyingSpaceMap (TheoremA.fiberInclusion F d) ≫
          classifyingSpaceMap (TheoremA.sourceProjection F)) x
      rw [← classifyingSpaceMap_comp, TheoremA.fiberInclusion_source]
    · apply ContinuousMap.ext
      intro t
      change (Path.delayReflRight 0 (HomotopyFiber.toPath _ _ (fiberComparison F d x))) t = _
      rw [Path.delayReflRight_zero]
      change ((HomotopyFiber.toPath _ _ (fiberComparison F d x)).trans
        (Path.refl (classifyingSpacePoint d))) t =
        (((TheoremA.comparisonClassifyingHomotopy F).symm.evalAt
          (classifyingSpaceMap (TheoremA.fiberInclusion F d) x)).symm.trans
          (HomotopyFiber.toPath _ _ (resolutionStrictFiberComparison F d x))) t
      simp only [Path.trans_apply, Path.symm_apply]
      split_ifs
      · change commaNullhomotopy F d (_, x) =
          TheoremA.comparisonClassifyingHomotopy F
            (σ (σ _), classifyingSpaceMap (TheoremA.fiberInclusion F d) x)
        rw [unitInterval.symm_symm, comparisonClassifyingHomotopy_restrict]
      · rfl
  map_one_left x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Path.toContinuousMap
        (Path.delayReflRight_one (HomotopyFiber.toPath _ _ (fiberComparison F d x)))

/-- The identification keeps the identity comma object's constant-path
basepoint fixed throughout the homotopy. -/
@[simp]
theorem resolutionComparisonHomotopy_identity (c : C) (t : I) :
    resolutionComparisonHomotopy F (F.obj c)
      (t, classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c)))) =
      HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMap_point F c) := by
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z => z.1.1) (fiberComparison_identity F c)
  · apply ContinuousMap.ext
    intro s
    change (fiberComparison F (F.obj c)
      (classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c))))).1.2 (qRight (s, t)) = _
    rw [fiberComparison_identity]
    rfl

end CategoryTheory.TheoremB
