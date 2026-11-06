/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FiberwiseBridge.WeakFibers
public import Colib.Topology.OpenGluing.FibrationSpan.RightWeakEquivalence

/-!
# Actual normalized bridge ends from weak original strict fibers

These theorems discharge the literal bridge-end base-change obligations
for arbitrary ambient parameter spaces. They use the original span maps,
actual cylinder compact lifting, and the source-collar locality proof.
Closed graph hypotheses are imposed on the original overlap base only.


Implementation provenance:
`Quillen/Topology/OpenGluing/FibrationSpan/BridgeBaseChange.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology.FiberwiseMappingPath
open TopCat.MappingCylinder


noncomputable section
open Topology TopCat
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.FibrationSpan.Data
open TopCat.MappingCylinder FiberwiseMappingPath
variable {T : TopCat.{u}} {U V : Set T} (d : FibrationSpan.Data T U V)

/-- The original left bridge target becomes weak after every ambient base
change, using only weak original strict fibers of the right attaching map. -/
theorem bridgeEnd0_baseChange_isWeak_of_weak_fibers
    (hp : HomotopyLiftingProperty (d.k1 ≫ d.q1).hom)
    (hq : HomotopyLiftingProperty d.q1.hom)
    (hM : CompactHomotopyLiftingProperty (TopCat.MappingCylinder.Compact.projection d.cylinder1
      d.q1).hom)
    (hf : ∀ t : (U ∩ V : Set T), IsWeakHomotopyEquivalence
      (HomotopyFiber.strictMapOver (d.k1 ≫ d.q1).hom d.q1.hom d.k1.hom rfl t))
    {D : Type u} [TopologicalSpace D] (a : C(D,T)) :
    IsWeakHomotopyEquivalence (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i0.hom a)
      := by
  let j : TopCat.of (U ∩ V : Set T) ⟶ T := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  exact TopCat.FiberwiseBridge.SourceCharts.leftTarget_baseChange_isWeak_of_weak_fibers
    d.cylinder0 d.cylinder1 d.bridge_isPushout d.q0 d.q1 d.square j Subtype.val_injective hp hq
      hM hf a

/-- The symmetric conclusion retains the original right bridge map. -/
theorem bridgeEnd1_baseChange_isWeak_of_weak_fibers
    (hp : HomotopyLiftingProperty (d.k0 ≫ d.q0).hom)
    (hq : HomotopyLiftingProperty d.q0.hom)
    (hM : CompactHomotopyLiftingProperty (TopCat.MappingCylinder.Compact.projection d.cylinder0
      d.q0).hom)
    (hf : ∀ t : (U ∩ V : Set T), IsWeakHomotopyEquivalence
      (HomotopyFiber.strictMapOver (d.k0 ≫ d.q0).hom d.q0.hom d.k0.hom rfl t))
    {D : Type u} [TopologicalSpace D] (a : C(D,T)) :
    IsWeakHomotopyEquivalence (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i1.hom a)
      := by
  let j : TopCat.of (U ∩ V : Set T) ⟶ T := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have h := TopCat.FiberwiseBridge.SourceCharts.leftTarget_baseChange_isWeak_of_weak_fibers
    d.cylinder1 d.cylinder0 d.bridge_isPushout.flip d.q1 d.q0 d.square.symm j
      Subtype.val_injective hp hq hM hf a
  rw [d.bridgeProjection_flipped] at h
  exact h

/-- Genuine end/source HLP and actual compact closed graphs supply all the
right cylinder lifting used to prove weakness of the left bridge end. -/
theorem bridgeEnd0_baseChange_isWeak_of_closedGraphs
    (hp1 : HomotopyLiftingProperty d.p1.hom)
    (hR : HomotopyLiftingProperty (d.k1 ≫ d.q1).hom)
    (hgraph : ∀ (D : Type u) [TopologicalSpace D] [CompactSpace D] [LocallyCompactSpace D]
      (b : C(D, (U ∩ V : Set T))),
        IsClosed (Set.ofPred (fun z : D × (U ∩ V : Set T) ↦ b z.1 = z.2)))
    (hf : ∀ t : (U ∩ V : Set T), IsWeakHomotopyEquivalence
      (HomotopyFiber.strictMapOver (d.k1 ≫ d.q1).hom d.q1.hom d.k1.hom rfl t))
    {D : Type u} [TopologicalSpace D] (a : C(D,T)) :
    IsWeakHomotopyEquivalence (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i0.hom a) :=
  d.bridgeEnd0_baseChange_isWeak_of_weak_fibers hR (d.q1_lifting hp1)
    (TopCat.MappingCylinder.Compact.compactHomotopyLiftingProperty_of_closedGraphs
      d.cylinder1 d.q1 hR (d.q1_lifting hp1) hgraph) hf a

/-- The same actual compact graph hypothesis supplies the other bridge end. -/
theorem bridgeEnd1_baseChange_isWeak_of_closedGraphs
    (hp0 : HomotopyLiftingProperty d.p0.hom)
    (hR : HomotopyLiftingProperty (d.k0 ≫ d.q0).hom)
    (hgraph : ∀ (D : Type u) [TopologicalSpace D] [CompactSpace D] [LocallyCompactSpace D]
      (b : C(D, (U ∩ V : Set T))),
        IsClosed (Set.ofPred (fun z : D × (U ∩ V : Set T) ↦ b z.1 = z.2)))
    (hf : ∀ t : (U ∩ V : Set T), IsWeakHomotopyEquivalence
      (HomotopyFiber.strictMapOver (d.k0 ≫ d.q0).hom d.q0.hom d.k0.hom rfl t))
    {D : Type u} [TopologicalSpace D] (a : C(D,T)) :
    IsWeakHomotopyEquivalence (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i1.hom a) :=
  d.bridgeEnd1_baseChange_isWeak_of_weak_fibers hR (d.q0_lifting hp0)
    (TopCat.MappingCylinder.Compact.compactHomotopyLiftingProperty_of_closedGraphs
      d.cylinder0 d.q0 hR (d.q0_lifting hp0) hgraph) hf a

end TopCat.FibrationSpan.Data
