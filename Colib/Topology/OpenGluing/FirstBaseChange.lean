/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.OpenGluing.FirstWeakEquivalence
public import Colib.Topology.DeformationRetract.FiberwiseBaseChange
public import Colib.Topology.FiberwiseMappingPath.BaseChangeCharts

/-! # Exact first-attachment weakness after arbitrary displayed base change

The actual target charts and the whole fiberwise local collar deformation
are pulled back directly. No preservation of a topological pushout is used.
Weakness of the literal base-changed bridge end remains an explicit input.


Implementation provenance:
`Quillen/Topology/OpenGluing/FirstBaseChange.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology.CubicalSubdivision
open Topology.FiberwiseMappingPath


noncomputable section
open Topology TopCat
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.OpenGluing.Data
open FiberwiseMappingPath CubicalSubdivision
variable {T : TopCat.{u}} {U V : Set T} (d : OpenGluing.Data T U V)
  (h : C(d.M, unitInterval)) (hi : ∀ a, h (d.i0 a) = 1)
  (cut : unitInterval) (hc : cut < 1)
  {D : Type u} [TopologicalSpace D] (g : C(D, T))

/-- The first-end collar restriction stays weak after every actual base map,
by pulling back its complete fiberwise strong deformation. -/
theorem firstEnd_baseChange_restriction_collar_weak
    (R : TopCat.CylinderStrongDeformationRetract (d.bridgeEndCollarEnd h hi cut hc))
    (hR : R.H ≫ d.bridgeEndCollarBase h cut =
      fst (d.BridgeEndCollar h cut) TopCat.I ≫ d.bridgeEndCollarBase h cut) :
    IsWeakHomotopyEquivalence (restriction (baseChangedMap d.firstBase.hom d.firstEnd.hom g)
      {z : BaseChangedTarget d.firstBase.hom g | z.val.2 ∈ d.firstEndCollarSet h hi cut}) := by
  apply baseChangedRestriction_isWeak_of_chart d.firstBase.hom d.firstEnd.hom g
    (d.firstEndCollarSet h hi cut) (d.firstEndCollarEnd h hi cut hc).hom
    (d.firstEndCollarBase h hi cut).hom
    (d.firstEndCollarSourceHomeomorph h hi cut hc) (Homeomorph.refl _)
    (fun _ ↦ rfl) (fun _ ↦ rfl)
  exact isWeakHomotopyEquivalence_of_homotopyEquiv
    ((d.firstEndCollarStrongDeformationRetract h hi cut hc R).baseChangeHomotopyEquiv
      (d.firstEndCollarBase h hi cut)
      (d.firstEndCollarStrongDeformationRetract_over h hi cut hc R hR) g)

/-- The pulled-back bridge chart retains exactly the original base-changed i0 map. -/
theorem firstEnd_baseChange_restriction_overlap_weak (hV : IsOpen V)
    (hweak : IsWeakHomotopyEquivalence (baseChangedMap d.bridgeBase.hom d.i0.hom g)) :
    IsWeakHomotopyEquivalence (restriction (baseChangedMap d.firstBase.hom d.firstEnd.hom g)
      {z : BaseChangedTarget d.firstBase.hom g | z.val.2 ∈ d.firstBase ⁻¹' V}) := by
  apply baseChangedRestriction_isWeak_of_chart d.firstBase.hom d.firstEnd.hom g
    (d.firstBase ⁻¹' V) d.i0.hom d.bridgeBase.hom
    d.firstEndOverlapSourceHomeomorph (d.bridgeChart hV)
  · intro x
    exact ConcreteCategory.congr_hom d.first_isPushout.w (d.firstEndOverlapSourceHomeomorph x)
  · intro y
    exact d.firstBridge_base_apply y
  · exact hweak

/-- The pulled-back intersection is weak from the genuine fiberwise local SDR. -/
theorem firstEnd_baseChange_restriction_intersection_weak (hV : IsOpen V)
    (R : TopCat.CylinderStrongDeformationRetract (d.bridgeEndCollarEnd h hi cut hc))
    (hR : R.H ≫ d.bridgeEndCollarBase h cut =
      fst (d.BridgeEndCollar h cut) TopCat.I ≫ d.bridgeEndCollarBase h cut) :
    IsWeakHomotopyEquivalence (restriction (baseChangedMap d.firstBase.hom d.firstEnd.hom g)
      {z : BaseChangedTarget d.firstBase.hom g |
        z.val.2 ∈ d.firstEndCollarSet h hi cut ∩ d.firstBase ⁻¹' V}) := by
  apply baseChangedRestriction_isWeak_of_chart d.firstBase.hom d.firstEnd.hom g
    (d.firstEndCollarSet h hi cut ∩ d.firstBase ⁻¹' V)
    (d.bridgeEndCollarEnd h hi cut hc).hom (d.bridgeEndCollarBase h cut).hom
    (d.firstEndIntersectionSourceHomeomorph h hi cut hc)
    (d.firstEndIntersectionTargetHomeomorph h hi cut hV)
  · intro x
    exact ConcreteCategory.congr_hom d.first_isPushout.w
      (d.firstEndIntersectionSourceHomeomorph h hi cut hc x)
  · intro y
    exact d.firstBridge_base_apply y.val
  · exact isWeakHomotopyEquivalence_of_homotopyEquiv
      (R.baseChangeHomotopyEquiv (d.bridgeEndCollarBase h cut) hR g)

/-- The original first-end map is weak after this arbitrary base change when
the original bridge-end map is weak after that same base change. Every local
restriction and the intersection are identified, and the new parameter is fixed. -/
theorem firstEnd_baseChange_isWeakHomotopyEquivalence (hV : IsOpen V)
    (R : TopCat.CylinderStrongDeformationRetract (d.bridgeEndCollarEnd h hi cut hc))
    (hR : R.H ≫ d.bridgeEndCollarBase h cut =
      fst (d.BridgeEndCollar h cut) TopCat.I ≫ d.bridgeEndCollarBase h cut)
    (hweak : IsWeakHomotopyEquivalence (baseChangedMap d.bridgeBase.hom d.i0.hom g)) :
    IsWeakHomotopyEquivalence (baseChangedMap d.firstBase.hom d.firstEnd.hom g) := by
  apply isWeakHomotopyEquivalence_of_two_open (baseChangedMap d.firstBase.hom d.firstEnd.hom g)
    {z : BaseChangedTarget d.firstBase.hom g | z.val.2 ∈ d.firstEndCollarSet h hi cut}
    {z : BaseChangedTarget d.firstBase.hom g | z.val.2 ∈ d.firstBase ⁻¹' V}
  · exact (d.firstEndCollar_isOpen h hi cut).preimage (by fun_prop)
  · exact (hV.preimage d.firstBase.hom.continuous).preimage (by fun_prop)
  · change (fun z : BaseChangedTarget d.firstBase.hom g ↦ z.val.2) ⁻¹'
      (d.firstEndCollarSet h hi cut ∪ d.firstBase ⁻¹' V) = Set.univ
    rw [d.firstEndCollar_cover h hi cut hc]
    rfl
  · exact d.firstEnd_baseChange_restriction_collar_weak h hi cut hc g R hR
  · exact d.firstEnd_baseChange_restriction_overlap_weak g hV hweak
  · exact d.firstEnd_baseChange_restriction_intersection_weak h hi cut hc g hV R hR

end TopCat.OpenGluing.Data
