/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.OpenGluing.FibrationSpan.FirstWeakEquivalence
public import Colib.Topology.OpenGluing.FirstBaseChange

/-! # Actual normalized first-end weakness over every supplied parameter

The original mapping cylinders supply the entire fiberwise collar deformation.
The only weak input is the literal bridge-end map after the same base change.
No compactness, local compactness, or pullback preservation of pushouts is used.


Implementation provenance:
`Quillen/Topology/OpenGluing/FibrationSpan/FirstBaseChange.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology.FiberwiseMappingPath


noncomputable section
open Topology TopCat
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
namespace TopCat.FibrationSpan.Data
open FiberwiseMappingPath
variable {T : TopCat.{u}} {U V : Set T} (d : FibrationSpan.Data T U V)

/-- The actual local SDR retains the original ambient base at every time. -/
theorem normalizedBridgeEndCollarSDR_over (cut : unitInterval) (hc : cut < 1) :
    (d.normalizedBridgeEndCollarSDR cut hc).H ≫
        d.normalized.bridgeEndCollarBase d.bridgeTargetHeight cut =
      fst (d.normalized.BridgeEndCollar d.bridgeTargetHeight cut) TopCat.I ≫
        d.normalized.bridgeEndCollarBase d.bridgeTargetHeight cut := by
  apply ConcreteCategory.hom_ext
  intro z
  exact congrArg Subtype.val (ConcreteCategory.congr_hom (d.bridgeTargetCollarSDR_over cut hc) z)

/-- The unchanged normalized first end is weak after this arbitrary base map,
provided the unchanged bridge end is weak after that same base map. -/
theorem firstEnd_baseChange_isWeakHomotopyEquivalence
    {D : Type u} [TopologicalSpace D] (g : C(D, T)) (hV : IsOpen V)
    (hweak : IsWeakHomotopyEquivalence
      (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i0.hom g)) :
    IsWeakHomotopyEquivalence
      (baseChangedMap d.normalized.firstBase.hom d.normalized.firstEnd.hom g) :=
  d.normalized.firstEnd_baseChange_isWeakHomotopyEquivalence d.bridgeTargetHeight
    d.bridgeTargetHeight_target 0 zero_lt_one g hV
    (d.normalizedBridgeEndCollarSDR 0 zero_lt_one)
    (d.normalizedBridgeEndCollarSDR_over 0 zero_lt_one) hweak

end TopCat.FibrationSpan.Data
