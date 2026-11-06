/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.UniversalComparison
public import Colib.Topology.OpenGluing.FibrationSpan.FirstBaseChange

/-!
# Universal strict-pullback comparison for the original normalized first chart

The original endpoint comparison is transferred through the exact first-end
map. Its arbitrary base-change weakness is proved using the actual fiberwise
local collar. The still-needed bridge-end base-change weakness remains
explicit; no global bridge deformation or first-projection HLP is assumed.


Implementation provenance:
`Quillen/Topology/OpenGluing/FirstUniversalComparison.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
namespace TopCat
namespace OpenGluing.Data
open FiberwiseMappingPath CubicalSubdivision
variable {T : TopCat.{u}} {U V : Set T} (d : OpenGluing.Data T U V)
  (h : C(d.M, unitInterval)) (hi : ∀ a, h (d.i0 a) = 1)
  (cut : unitInterval) (hc : cut < 1)

/-- The original first projection has universal comparison weakness from
its endpoint's universal comparison, the genuine local fiberwise collar,
and the actual bridge end's universal base-change weakness. -/
theorem firstProjection_universalStrictPullbackComparison (hV : IsOpen V)
    (R : TopCat.CylinderStrongDeformationRetract (d.bridgeEndCollarEnd h hi cut hc))
    (hR : R.H ≫ d.bridgeEndCollarBase h cut =
      fst (d.BridgeEndCollar h cut) TopCat.I ≫ d.bridgeEndCollarBase h cut)
    (hp0 : UniversalStrictPullbackComparison d.p0.hom)
    (hbridge : ∀ (D : Type u) [TopologicalSpace D] (g : C(D, T)),
      IsWeakHomotopyEquivalence (baseChangedMap d.bridgeBase.hom d.i0.hom g)) :
    UniversalStrictPullbackComparison d.firstProjection.hom := by
  apply UniversalStrictPullbackComparison.of_baseChanges d.firstProjection.hom d.firstEnd.hom
  · have he : d.firstProjection.hom.comp d.firstEnd.hom = d.p0.hom :=
      congrArg TopCat.Hom.hom d.firstEnd_projection
    rw [he]
    exact hp0
  · intro D _ g
    let i : C(U,T) := ⟨Subtype.val,continuous_subtype_val⟩
    apply baseChangedMap_isWeak_of_injective_base d.firstProjection.hom d.firstEnd.hom g
      i Subtype.val_injective
    exact d.firstEnd_baseChange_isWeakHomotopyEquivalence h hi cut hc (i.comp g) hV R hR
      (hbridge D (i.comp g))

/-- Genuine compact HLP of the original endpoint is a sufficient comparison
input; no HLP of the first projection or its open parameter loci is inferred. -/
theorem firstProjection_universalStrictPullbackComparison_of_compact (hV : IsOpen V)
    (R : TopCat.CylinderStrongDeformationRetract (d.bridgeEndCollarEnd h hi cut hc))
    (hR : R.H ≫ d.bridgeEndCollarBase h cut =
      fst (d.BridgeEndCollar h cut) TopCat.I ≫ d.bridgeEndCollarBase h cut)
    (hp0 : CompactHomotopyLiftingProperty d.p0.hom)
    (hbridge : ∀ (D : Type u) [TopologicalSpace D] (g : C(D, T)),
      IsWeakHomotopyEquivalence (baseChangedMap d.bridgeBase.hom d.i0.hom g)) :
    UniversalStrictPullbackComparison d.firstProjection.hom :=
  d.firstProjection_universalStrictPullbackComparison h hi cut hc hV R hR
    hp0.universalStrictPullbackComparison hbridge

/-- The actual left-chart homeomorphism identifies its projection with the
unchanged first projection, so the pool's literal local restriction gets the
same universal comparison property. -/
theorem leftRestriction_universalStrictPullbackComparison (hU : IsOpen U)
    (hp : UniversalStrictPullbackComparison d.firstProjection.hom) :
    UniversalStrictPullbackComparison (restriction d.projection.hom U) := by
  apply UniversalStrictPullbackComparison.of_homeomorph
    (restriction d.projection.hom U) (d.leftChart hU)
  have he : (restriction d.projection.hom U).comp
      ((d.leftChart hU) : C(d.First,{z : d.Total // d.projection z ∈ U})) =
        d.firstProjection.hom := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact d.totalFirst_projection_apply x
  rw [he]
  exact hp

end OpenGluing.Data
namespace FibrationSpan.Data
open FiberwiseMappingPath CubicalSubdivision
variable {T : TopCat.{u}} {U V : Set T} (d : FibrationSpan.Data T U V)

/-- The original mapping cylinders supply all local collar data. The only
additional weak input is the unchanged bridge end after arbitrary base change. -/
theorem firstProjection_universalStrictPullbackComparison (hV : IsOpen V)
    (hp0 : UniversalStrictPullbackComparison d.p0.hom)
    (hbridge : ∀ (D : Type u) [TopologicalSpace D] (g : C(D, T)),
      IsWeakHomotopyEquivalence
        (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i0.hom g)) :
    UniversalStrictPullbackComparison d.normalized.firstProjection.hom :=
  d.normalized.firstProjection_universalStrictPullbackComparison d.bridgeTargetHeight
    d.bridgeTargetHeight_target 0 zero_lt_one hV
    (d.normalizedBridgeEndCollarSDR 0 zero_lt_one)
    (d.normalizedBridgeEndCollarSDR_over 0 zero_lt_one) hp0 hbridge

/-- Compact HLP of the original left endpoint suffices for the concrete
normalized first-projection comparison. -/
theorem firstProjection_universalStrictPullbackComparison_of_compact (hV : IsOpen V)
    (hp0 : CompactHomotopyLiftingProperty d.p0.hom)
    (hbridge : ∀ (D : Type u) [TopologicalSpace D] (g : C(D, T)),
      IsWeakHomotopyEquivalence
        (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i0.hom g)) :
    UniversalStrictPullbackComparison d.normalized.firstProjection.hom :=
  d.firstProjection_universalStrictPullbackComparison hV hp0.universalStrictPullbackComparison
    hbridge

/-- The literal left restriction used by path pools inherits the concrete
first-model comparison through its actual original chart homeomorphism. -/
theorem leftRestriction_universalStrictPullbackComparison_of_compact
    (hU : IsOpen U) (hV : IsOpen V) (hp0 : CompactHomotopyLiftingProperty d.p0.hom)
    (hbridge : ∀ (D : Type u) [TopologicalSpace D] (g : C(D, T)),
      IsWeakHomotopyEquivalence
        (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i0.hom g)) :
    UniversalStrictPullbackComparison (restriction d.normalized.projection.hom U) :=
  d.normalized.leftRestriction_universalStrictPullbackComparison hU
    (d.firstProjection_universalStrictPullbackComparison_of_compact hV hp0 hbridge)

end FibrationSpan.Data
end TopCat
