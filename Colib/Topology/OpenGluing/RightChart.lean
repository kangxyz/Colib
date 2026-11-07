/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.OpenGluing.FirstBaseChange
public import Colib.Topology.FiberwiseMappingPath.BaseChangeTransport

/-! # The actual right normalized chart as the reversed first attachment

Swapping the two ends leaves the bridge unchanged. The original right-chart
pushout supplies an explicit coordinate homeomorphism from the swapped first
attachment, retaining its endpoint and ambient base. Ordinary weakness and
its actual base changes then transfer to the unchanged original right end.


Implementation provenance:
`Quillen/Topology/OpenGluing/RightChart.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology.FiberwiseMappingPath


noncomputable section
open Topology TopCat
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.OpenGluing.Data
open FiberwiseMappingPath
variable {T : TopCat.{u}} {U V : Set T} (d : OpenGluing.Data T U V)

/-- Reverse the two ends, retaining the original bridge and both attaching maps. -/
def swapped : OpenGluing.Data T V U where
  E0 := d.E1
  E1 := d.E0
  M := d.M
  p0 := d.p1
  p1 := d.p0
  q := TopCat.ofHom ⟨fun m ↦ ⟨(d.q m).val,(d.q m).property.2,(d.q m).property.1⟩,by fun_prop⟩
  i0 := d.i1
  i1 := d.i0
  over0 := d.over1
  over1 := d.over0

/-- The original right chart retains the ambient displayed base. -/
def rightBase : d.RightChart ⟶ T :=
  TopCat.ofHom ⟨fun x ↦ d.projection x.val,by fun_prop⟩

/-- The actual right restricted pushout is the swapped first pushout. -/
def rightFirstIso (hV : IsOpen V) : d.swapped.First ≅ d.RightChart :=
  d.swapped.first_isPushout.isoIsPushout d.M d.E1 (d.right_isPushout hV)

/-- For open `V`, identify the first attachment of the swapped gluing data with the original
right chart. -/
def rightFirstHomeomorph (hV : IsOpen V) : d.swapped.First ≃ₜ d.RightChart :=
  TopCat.homeoOfIso (d.rightFirstIso hV)

@[reassoc (attr := simp)] theorem rightFirstIso_bridge (hV : IsOpen V) :
    d.swapped.firstBridge ≫ (d.rightFirstIso hV).hom = d.rightBridge :=
  d.swapped.first_isPushout.inl_isoIsPushout_hom _ _ (d.right_isPushout hV)

@[reassoc (attr := simp)] theorem rightFirstIso_end (hV : IsOpen V) :
    d.swapped.firstEnd ≫ (d.rightFirstIso hV).hom = d.rightEnd :=
  d.swapped.first_isPushout.inr_isoIsPushout_hom _ _ (d.right_isPushout hV)

@[simp] theorem rightFirstHomeomorph_bridge (hV : IsOpen V) (m : d.M) :
    d.rightFirstHomeomorph hV (d.swapped.firstBridge m) = d.rightBridge m :=
  ConcreteCategory.congr_hom (d.rightFirstIso_bridge hV) m

@[simp] theorem rightFirstHomeomorph_end (hV : IsOpen V) (e : d.E1) :
    d.rightFirstHomeomorph hV (d.swapped.firstEnd e) = d.rightEnd e :=
  ConcreteCategory.congr_hom (d.rightFirstIso_end hV) e

/-- Every original base coordinate is retained by the right-chart identification. -/
theorem rightFirstHomeomorph_base (hV : IsOpen V) (x : d.swapped.First) :
    d.rightBase (d.rightFirstHomeomorph hV x) = d.swapped.firstBase x := by
  rcases Types.eq_or_eq_of_isPushout (d.swapped.first_isPushout.map (forget TopCat)) x with
    ⟨m,hm⟩ | ⟨e,he⟩
  · change d.swapped.firstBridge m = x at hm
    rw [← hm,d.rightFirstHomeomorph_bridge,d.swapped.firstBridge_base_apply]
    change d.projection (d.totalFirst (d.firstBridge m)) = (d.q m).val
    rw [d.totalFirst_projection_apply,d.firstBridge_base_apply]
  · change d.swapped.firstEnd e = x at he
    rw [← he,d.rightFirstHomeomorph_end,d.swapped.firstEnd_base_apply]
    exact d.totalEnd_projection_apply e

variable (h : C(d.M, unitInterval)) (hi : ∀ a, h (d.i1 a) = 1)
  (cut : unitInterval) (hc : cut < 1)
  (hU : IsOpen U) (hV : IsOpen V)
  (R : TopCat.CylinderStrongDeformationRetract (d.swapped.bridgeEndCollarEnd h hi cut hc))

include h hi cut hc hU hV R in
/-- The original right endpoint into its actual open chart is weak. -/
theorem rightEnd_isWeakHomotopyEquivalence
    (hweak : IsWeakHomotopyEquivalence d.i1.hom) :
    IsWeakHomotopyEquivalence d.rightEnd.hom := by
  have heq : (d.rightFirstHomeomorph hV).toHomotopyEquiv.toFun.comp d.swapped.firstEnd.hom =
      d.rightEnd.hom := by
    ext e
    exact congrArg Subtype.val (d.rightFirstHomeomorph_end hV e)
  rw [← heq]
  exact (isWeakHomotopyEquivalence_of_homotopyEquiv (d.rightFirstHomeomorph
    hV).toHomotopyEquiv).comp
    (d.swapped.firstEnd_isWeakHomotopyEquivalence h hi cut hc hU R hweak)

include hU hV in
/-- The original right endpoint stays weak after this actual base change,
using exactly the base-changed original right bridge-end input. -/
theorem rightEnd_baseChange_isWeakHomotopyEquivalence
    (hR : R.H ≫ d.swapped.bridgeEndCollarBase h cut =
      fst (d.swapped.BridgeEndCollar h cut) TopCat.I ≫ d.swapped.bridgeEndCollarBase h cut)
    {D : Type u} [TopologicalSpace D] (g : C(D, T))
    (hweak : IsWeakHomotopyEquivalence (baseChangedMap d.bridgeBase.hom d.i1.hom g)) :
    IsWeakHomotopyEquivalence (baseChangedMap d.rightBase.hom d.rightEnd.hom g) := by
  apply baseChangedMap_isWeak_of_targetHomeomorph d.rightBase.hom d.rightEnd.hom g
    d.swapped.firstBase.hom d.swapped.firstEnd.hom (d.rightFirstHomeomorph hV)
    (d.rightFirstHomeomorph_end hV) (d.rightFirstHomeomorph_base hV)
  exact d.swapped.firstEnd_baseChange_isWeakHomotopyEquivalence h hi cut hc g hU R hR hweak

end TopCat.OpenGluing.Data
