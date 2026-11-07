/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.PathSubdivision.GlobalComparison
public import Colib.Topology.OpenGluing.FirstUniversalComparison
public import Colib.Topology.OpenGluing.FibrationSpan.RightWeakEquivalence
public import Colib.Topology.OpenGluing.CartesianCharts
public import Colib.Topology.Realization.CompactGraph
public import Colib.Topology.OpenGluing.FibrationSpan.BridgeBaseChange

/-!
# Original normalized charts and the global weak pullback comparison

The actual left, right, and overlap chart identifications feed the generic
finite path-subdivision theorem. The final theorem constructs the bridge-end base-change inputs
    from actual
endpoint/common-source fibrations, weak original strict fiber maps, and the
closed graphs needed for compact cylinder lifting. No bridge weakness,
global lifting property, or chosen continuous inverse is assumed.


Implementation provenance:
`Quillen/Topology/OpenGluing/GlobalWeakComparison.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval Simplicial
universe u
namespace TopCat
namespace OpenGluing.Data
open CubicalSubdivision
variable {T : TopCat.{u}} {U V : Set T} (d : OpenGluing.Data T U V)

/-- The original bridge is exactly the actual overlap of the two total charts. -/
def overlapChart (hU : IsOpen U) (hV : IsOpen V) :
    d.M ≃ₜ {z : d.Total // d.projection z ∈ U ∩ V} := by
  let e : {x : d.First // d.firstBase x ∈ V} ≃ₜ
      {x : {z : d.Total // d.projection z ∈ U} // d.projection x.val ∈ V} :=
    (d.leftChart hU).subtype (fun x ↦ by
      change d.firstBase x ∈ V ↔ d.projection (d.totalFirst x) ∈ V
      rw [d.totalFirst_projection_apply])
  let flatten : {x : {z : d.Total // d.projection z ∈ U} // d.projection x.val ∈ V} ≃ₜ
      {z : d.Total // d.projection z ∈ U ∩ V} := {
    toFun x := ⟨x.val.val,x.val.property,x.property⟩
    invFun z := ⟨⟨z.val,z.property.1⟩,z.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  exact (d.bridgeChart hV).trans (e.trans flatten)

@[simp] theorem overlapChart_apply (hU : IsOpen U) (hV : IsOpen V) (m : d.M) :
    (d.overlapChart hU hV m).val = d.totalFirst (d.firstBridge m) := rfl

/-- The actual overlap homeomorphism retains the original entire base point. -/
theorem overlapChart_projection (hU : IsOpen U) (hV : IsOpen V) :
    (restriction d.projection.hom (U ∩ V)).comp
      ((d.overlapChart hU hV) : C(d.M,{z : d.Total // d.projection z ∈ U ∩ V})) = d.q.hom := by
  apply ContinuousMap.ext
  intro m
  apply Subtype.ext
  exact (d.totalFirst_projection_apply _).trans (d.firstBridge_base_apply m)

/-- The genuine overlap projection supplies the literal local restriction
used by the path pools, through the displayed original chart homeomorphism. -/
theorem overlapRestriction_universalStrictPullbackComparison
    (hU : IsOpen U) (hV : IsOpen V) (hq : UniversalStrictPullbackComparison d.q.hom) :
    UniversalStrictPullbackComparison (restriction d.projection.hom (U ∩ V)) := by
  apply UniversalStrictPullbackComparison.of_homeomorph
    (restriction d.projection.hom (U ∩ V)) (d.overlapChart hU hV)
  rw [d.overlapChart_projection]
  exact hq

/-- A genuine realization model of the ambient base supplies every required
compact closed graph in the actual overlap subspace. The overlap need not
itself be presented as a simplicial realization. -/
theorem overlap_closedGraphs_of_realizationModel
    (X : SSet.{u}) (e : T ≃ₜ |X|)
    (D : Type u) [TopologicalSpace D] [CompactSpace D]
    (b : C(D, (U ∩ V : Set T))) :
    IsClosed (Set.ofPred (fun z : D × (U ∩ V : Set T) ↦ b z.1 = z.2)) := by
  let b' : C(D,|X|) := ⟨fun x ↦ e (b x).val,by fun_prop⟩
  have hc := (realization_compactMap_isClosed_graph X b').preimage
    (show Continuous (fun z : D × (U ∩ V : Set T) ↦ (z.1,e z.2.val)) from by fun_prop)
  convert hc using 1
  ext z
  change (b z.1 = z.2) ↔ e (b z.1).val = e z.2.val
  exact ⟨fun h ↦ congrArg (fun x : (U ∩ V : Set T) ↦ e x.val) h,
    fun h ↦ Subtype.ext (e.injective h)⟩

/-- The unchanged left endpoint chart comparison factors through the literal
strict pullback inclusion, with its original endpoint and entire constant path. -/
theorem leftComparison_isWeakHomotopyEquivalence (hU : IsOpen U)
    (hfirst : IsWeakHomotopyEquivalence d.firstEnd.hom)
    (hp : UniversalStrictPullbackComparison d.projection.hom) :
    IsWeakHomotopyEquivalence d.leftComparison := by
  let e := HomotopyPullback.preimageStrictPullbackHomeomorph d.projection.hom U
  have hw := (hp U d.leftBaseInclusion).comp
    ((isWeakHomotopyEquivalence_of_homotopyEquiv e.toHomotopyEquiv).comp
      ((isWeakHomotopyEquivalence_of_homotopyEquiv (d.leftChart hU).toHomotopyEquiv).comp hfirst))
  have he : (HomotopyPullback.strictPullbackInclusion d.projection.hom d.leftBaseInclusion).comp
      (e.toHomotopyEquiv.toFun.comp ((d.leftChart hU).toHomotopyEquiv.toFun.comp d.firstEnd.hom)) =
        d.leftComparison := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (ConcreteCategory.congr_hom d.totalLeft_projection x)
    · refine Prod.ext rfl ?_
      apply ContinuousMap.ext
      intro t
      exact ConcreteCategory.congr_hom d.totalLeft_projection x
  exact he ▸ hw

/-- The unchanged right chart comparison is weak from the actual right-end
weakness and the original total's universal comparison. -/
theorem rightComparison_isWeakHomotopyEquivalence
    (hright : IsWeakHomotopyEquivalence d.rightEnd.hom)
    (hp : UniversalStrictPullbackComparison d.projection.hom) :
    IsWeakHomotopyEquivalence d.rightComparison := by
  let e := HomotopyPullback.preimageStrictPullbackHomeomorph d.projection.hom V
  have hw := (hp V d.rightBaseInclusion).comp
    ((isWeakHomotopyEquivalence_of_homotopyEquiv e.toHomotopyEquiv).comp hright)
  have he : (HomotopyPullback.strictPullbackInclusion d.projection.hom d.rightBaseInclusion).comp
      (e.toHomotopyEquiv.toFun.comp d.rightEnd.hom) = d.rightComparison := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (d.totalEnd_projection_apply x)
    · refine Prod.ext rfl ?_
      apply ContinuousMap.ext
      intro t
      exact d.totalEnd_projection_apply x
  exact he ▸ hw

end OpenGluing.Data
namespace FibrationSpan.Data
open FiberwiseMappingPath CubicalSubdivision
variable {T : TopCat.{u}} {U V : Set T} (d : FibrationSpan.Data T U V)

/-- Transfer the right endpoint comparison through its actual base-changed
right-end map; all collar geometry is the span's constructed geometry. -/
theorem rightProjection_universalStrictPullbackComparison
    (hU : IsOpen U) (hV : IsOpen V)
    (hp1 : UniversalStrictPullbackComparison d.p1.hom)
    (hbridge : ∀ (D : Type u) [TopologicalSpace D] (g : C(D, T)),
      IsWeakHomotopyEquivalence
        (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i1.hom g)) :
    UniversalStrictPullbackComparison d.normalized.rightProjection.hom := by
  apply UniversalStrictPullbackComparison.of_baseChanges
    d.normalized.rightProjection.hom d.normalized.rightEnd.hom
  · have he : d.normalized.rightProjection.hom.comp d.normalized.rightEnd.hom = d.p1.hom :=
      congrArg TopCat.Hom.hom d.normalized.rightEnd_projection
    rw [he]
    exact hp1
  · intro D _ g
    let i : C(V,T) := ⟨Subtype.val,continuous_subtype_val⟩
    apply baseChangedMap_isWeak_of_injective_base d.normalized.rightProjection.hom
      d.normalized.rightEnd.hom g i Subtype.val_injective
    exact d.rightEnd_baseChange_isWeakHomotopyEquivalence (i.comp g) hU hV (hbridge D (i.comp g))

/-- The literal bridge projection inherits its universal comparison from
the original left overlap fibration and the actual left bridge-end base changes. -/
theorem bridgeProjection_universalStrictPullbackComparison
    (hq0 : UniversalStrictPullbackComparison d.q0.hom)
    (hbridge : ∀ (D : Type u) [TopologicalSpace D] (g : C(D, T)),
      IsWeakHomotopyEquivalence
        (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i0.hom g)) :
    UniversalStrictPullbackComparison d.bridgeProjection.hom := by
  apply UniversalStrictPullbackComparison.of_baseChanges d.bridgeProjection.hom d.normalized.i0.hom
  · have he : d.bridgeProjection.hom.comp d.normalized.i0.hom = d.q0.hom := by
      apply ContinuousMap.ext
      intro x
      exact Subtype.ext (d.normalized.over0 x)
    rw [he]
    exact hq0
  · intro D _ g
    let i : C((U ∩ V : Set T),T) := ⟨Subtype.val,continuous_subtype_val⟩
    apply baseChangedMap_isWeak_of_injective_base d.bridgeProjection.hom
      d.normalized.i0.hom g i Subtype.val_injective
    exact hbridge D (i.comp g)

/-- Sharp conditional assembly for the actual normalized total. The extra
bridge hypotheses are genuine universal base-change weaknesses, not ordinary
weakness of the bridge ends. Subsequent geometric assembly must supply them. -/
theorem universalStrictPullbackComparison_of_bridgeBaseChanges
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hp0 : HomotopyLiftingProperty d.p0.hom) (hp1 : HomotopyLiftingProperty d.p1.hom)
    (hbridge0 : ∀ (D : Type u) [TopologicalSpace D] (g : C(D, T)),
      IsWeakHomotopyEquivalence
        (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i0.hom g))
    (hbridge1 : ∀ (D : Type u) [TopologicalSpace D] (g : C(D, T)),
      IsWeakHomotopyEquivalence
        (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i1.hom g)) :
    UniversalStrictPullbackComparison d.normalized.projection.hom := by
  apply PathSubdivision.universalStrictPullbackComparison_of_two_open
    d.normalized.projection.hom U V hU hV hcover
  · exact d.leftRestriction_universalStrictPullbackComparison_of_compact hU hV hp0.compact hbridge0
  · exact d.rightProjection_universalStrictPullbackComparison hU hV
      hp1.compact.universalStrictPullbackComparison hbridge1
  · exact d.normalized.overlapRestriction_universalStrictPullbackComparison hU hV
      (d.bridgeProjection_universalStrictPullbackComparison
        (d.q0_lifting hp0).compact.universalStrictPullbackComparison hbridge0)

section WeakFibers
variable (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
  (hp0 : HomotopyLiftingProperty d.p0.hom) (hp1 : HomotopyLiftingProperty d.p1.hom)
  (hR : HomotopyLiftingProperty (d.k0 ≫ d.q0).hom)
  (hgraph : ∀ (D : Type u) [TopologicalSpace D] [CompactSpace D] [LocallyCompactSpace D]
    (b : C(D, (U ∩ V : Set T))), IsClosed (Set.ofPred (fun z : D × (U ∩ V : Set T) ↦ b z.1 = z.2)))
  (hf0 : ∀ t : (U ∩ V : Set T), IsWeakHomotopyEquivalence
    (HomotopyFiber.strictMapOver (d.k0 ≫ d.q0).hom d.q0.hom d.k0.hom rfl t))
  (hf1 : ∀ t : (U ∩ V : Set T), IsWeakHomotopyEquivalence
    (HomotopyFiber.strictMapOver (d.k1 ≫ d.q1).hom d.q1.hom d.k1.hom rfl t))
include hU hV hcover hp0 hp1 hR hgraph hf0 hf1

/-- Global universal weakness of the original normalized strict comparison.
All bridge-end comparisons are derived from the genuine source-collar charts,
actual compact cylinder lifting, and the weak original attaching strict fibers. -/
theorem universalStrictPullbackComparison_of_weak_fibers :
    UniversalStrictPullbackComparison d.normalized.projection.hom := by
  have hR1 : HomotopyLiftingProperty (d.k1 ≫ d.q1).hom := by
    rw [← d.square]
    exact hR
  exact d.universalStrictPullbackComparison_of_bridgeBaseChanges hU hV hcover hp0 hp1
    (fun _ _ a ↦ d.bridgeEnd0_baseChange_isWeak_of_closedGraphs hp1 hR1 hgraph hf1 a)
    (fun _ _ a ↦ d.bridgeEnd1_baseChange_isWeak_of_closedGraphs hp0 hR hgraph hf0 a)

/-- The actual constant-path comparison is weak after every original base
change, including empty sources and zero-dimensional tests. -/
theorem strictPullbackInclusion_isWeakHomotopyEquivalence_of_weak_fibers
    {S : Type u} [TopologicalSpace S] (a : C(S, T)) :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.strictPullbackInclusion d.normalized.projection.hom a) :=
  d.universalStrictPullbackComparison_of_weak_fibers hU hV hcover hp0 hp1 hR hgraph hf0 hf1 S a

/-- The original left endpoint chart is weak-cartesian with its exact
canonical constant-path comparison. -/
theorem leftComparison_isWeakHomotopyEquivalence_of_weak_fibers :
    IsWeakHomotopyEquivalence d.normalized.leftComparison := by
  have hR1 : HomotopyLiftingProperty (d.k1 ≫ d.q1).hom := by
    rw [← d.square]
    exact hR
  have hi := isWeakHomotopyEquivalence_of_baseChangedMap_id d.normalized.bridgeBase.hom
    d.normalized.i0.hom
      (d.bridgeEnd0_baseChange_isWeak_of_closedGraphs hp1 hR1 hgraph hf1 (ContinuousMap.id T))
  exact d.normalized.leftComparison_isWeakHomotopyEquivalence hU
    (d.firstEnd_isWeakHomotopyEquivalence hV hi)
    (d.universalStrictPullbackComparison_of_weak_fibers hU hV hcover hp0 hp1 hR hgraph hf0 hf1)

/-- The matching original right endpoint chart is weak-cartesian, without
replacing its actual map by a chosen weak inverse. -/
theorem rightComparison_isWeakHomotopyEquivalence_of_weak_fibers :
    IsWeakHomotopyEquivalence d.normalized.rightComparison := by
  have hi := isWeakHomotopyEquivalence_of_baseChangedMap_id d.normalized.bridgeBase.hom
    d.normalized.i1.hom
      (d.bridgeEnd1_baseChange_isWeak_of_closedGraphs hp0 hR hgraph hf0 (ContinuousMap.id T))
  exact d.normalized.rightComparison_isWeakHomotopyEquivalence
    (d.rightEnd_isWeakHomotopyEquivalence hU hV hi)
    (d.universalStrictPullbackComparison_of_weak_fibers hU hV hcover hp0 hp1 hR hgraph hf0 hf1)

end WeakFibers

/-- A genuine ambient realization model discharges all compact overlap graph
conditions in the weak-input normalized global comparison. -/
theorem universalStrictPullbackComparison_of_weak_fibers_realizationModel
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hp0 : HomotopyLiftingProperty d.p0.hom) (hp1 : HomotopyLiftingProperty d.p1.hom)
    (hR : HomotopyLiftingProperty (d.k0 ≫ d.q0).hom)
    (X : SSet.{u}) (e : T ≃ₜ |X|)
    (hf0 : ∀ t : (U ∩ V : Set T), IsWeakHomotopyEquivalence
      (HomotopyFiber.strictMapOver (d.k0 ≫ d.q0).hom d.q0.hom d.k0.hom rfl t))
    (hf1 : ∀ t : (U ∩ V : Set T), IsWeakHomotopyEquivalence
      (HomotopyFiber.strictMapOver (d.k1 ≫ d.q1).hom d.q1.hom d.k1.hom rfl t)) :
    UniversalStrictPullbackComparison d.normalized.projection.hom :=
  d.universalStrictPullbackComparison_of_weak_fibers hU hV hcover hp0 hp1 hR
    (fun D _ _ _ b ↦
      OpenGluing.Data.overlap_closedGraphs_of_realizationModel X e D b) hf0 hf1

end FibrationSpan.Data
end TopCat
