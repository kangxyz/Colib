/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.OpenGluing.FirstCollar
public import Colib.Topology.Homotopy.HomotopyGroup.WeakLocality

/-! # Ordinary weakness of the original first normalized attachment

The end collar, the genuine bridge chart, and their exact intersection form
the three restrictions used in ordinary two-open locality. Both collar maps
are actual strong deformation retract inclusions. The only remaining weak
input is the original whole-bridge attaching map; no arbitrary restriction
or base change of that weak map is inferred.


Implementation provenance:
`Quillen/Topology/OpenGluing/FirstWeakEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology

open Topology.CubicalSubdivision


noncomputable section
open Topology TopCat
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.OpenGluing.Data
open CubicalSubdivision
variable {T : TopCat.{u}} {U V : Set T} (d : OpenGluing.Data T U V)
  (h : C(d.M, unitInterval)) (hi : ∀ a, h (d.i0 a) = 1)
  (cut : unitInterval) (hc : cut < 1)

/-- The whole original end is precisely the source of the end-collar restriction. -/
def firstEndCollarSourceHomeomorph :
    {e : d.E0 // d.firstEnd e ∈ d.firstEndCollarSet h hi cut} ≃ₜ d.E0 where
  toFun := Subtype.val
  invFun e := ⟨e,(d.firstEndCollarEnd h hi cut hc e).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := by fun_prop

/-- The source over the genuine bridge chart is exactly the original overlap end. -/
def firstEndOverlapSourceHomeomorph :
    {e : d.E0 // d.firstEnd e ∈ d.firstBase ⁻¹' V} ≃ₜ d.Q0 where
  toFun e := ⟨e.val,by
    have he := e.property
    change d.firstBase (d.firstEnd e.val) ∈ V at he
    rw [d.firstEnd_base_apply] at he
    exact he⟩
  invFun e := ⟨e.val,by
    change d.firstBase (d.firstEnd e.val) ∈ V
    rw [d.firstEnd_base_apply]
    exact e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Intersecting with the collar does not remove any point of the overlap end. -/
def firstEndIntersectionSourceHomeomorph :
    {e : d.E0 // d.firstEnd e ∈
      d.firstEndCollarSet h hi cut ∩ d.firstBase ⁻¹' V} ≃ₜ d.Q0 where
  toFun e := d.firstEndOverlapSourceHomeomorph ⟨e.val,e.property.2⟩
  invFun e := ⟨e.val,(d.firstEndCollarEnd h hi cut hc e.val).property,
    (d.firstEndOverlapSourceHomeomorph.symm e).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The actual target intersection is the original local bridge collar. -/
def firstEndIntersectionTargetHomeomorph (hV : IsOpen V) :
    d.BridgeEndCollar h cut ≃ₜ
      (d.firstEndCollarSet h hi cut ∩ d.firstBase ⁻¹' V : Set d.First) where
  toFun m := ⟨d.firstBridge m.val,(d.firstEndCollarBridge h hi cut m).property,
    (d.bridgeChart hV m.val).property⟩
  invFun x := ⟨(d.bridgeChart hV).symm ⟨x.val,x.property.2⟩,by
    have he := congrArg Subtype.val ((d.bridgeChart hV).apply_symm_apply
      ⟨x.val,x.property.2⟩)
    change d.firstBridge ((d.bridgeChart hV).symm ⟨x.val,x.property.2⟩) = x.val at he
    have hx := x.property.1
    change cut < (d.firstCollarHeight h hi x.val).down at hx
    rw [← he,d.firstCollarHeight_bridge] at hx
    exact hx⟩
  left_inv m := by
    apply Subtype.ext
    exact (d.bridgeChart hV).symm_apply_apply m.val
  right_inv x := by
    apply Subtype.ext
    change d.firstBridge ((d.bridgeChart hV).symm ⟨x.val,x.property.2⟩) = x.val
    exact congrArg (fun z : {e : d.First // d.firstBase e ∈ V} ↦ z.val)
      ((d.bridgeChart hV).apply_symm_apply ⟨x.val,x.property.2⟩)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem firstEndIntersectionTargetHomeomorph_val (hV : IsOpen V)
    (m : d.BridgeEndCollar h cut) :
    (d.firstEndIntersectionTargetHomeomorph h hi cut hV m).val = d.firstBridge m.val := rfl

/-- On the end collar the original restricted map is the pushed-out local SDR. -/
theorem firstEnd_restriction_collar_weak
    (R : TopCat.CylinderStrongDeformationRetract (d.bridgeEndCollarEnd h hi cut hc)) :
    IsWeakHomotopyEquivalence (restriction d.firstEnd.hom (d.firstEndCollarSet h hi cut)) := by
  have heq : (d.firstEndCollarEnd h hi cut hc).hom.comp
      (d.firstEndCollarSourceHomeomorph h hi cut hc).toHomotopyEquiv.toFun =
      restriction d.firstEnd.hom (d.firstEndCollarSet h hi cut) := by
    ext e
    rfl
  rw [← heq]
  exact (isWeakHomotopyEquivalence_of_homotopyEquiv
    (d.firstEndCollarStrongDeformationRetract h hi cut hc R).toHomotopyEquiv).comp
      (isWeakHomotopyEquivalence_of_homotopyEquiv
        (d.firstEndCollarSourceHomeomorph h hi cut hc).toHomotopyEquiv)

/-- Over the original bridge chart the original restricted map is exactly i0. -/
theorem firstEnd_restriction_overlap_weak (hV : IsOpen V)
    (hweak : IsWeakHomotopyEquivalence d.i0.hom) :
    IsWeakHomotopyEquivalence (restriction d.firstEnd.hom (d.firstBase ⁻¹' V)) := by
  have heq : (d.bridgeChart hV).toHomotopyEquiv.toFun.comp
      (d.i0.hom.comp d.firstEndOverlapSourceHomeomorph.toHomotopyEquiv.toFun) =
      restriction d.firstEnd.hom (d.firstBase ⁻¹' V) := by
    apply ContinuousMap.ext
    intro e
    exact Subtype.ext (ConcreteCategory.congr_hom d.first_isPushout.w
      (d.firstEndOverlapSourceHomeomorph e))
  rw [← heq]
  exact (isWeakHomotopyEquivalence_of_homotopyEquiv (d.bridgeChart hV).toHomotopyEquiv).comp
    (hweak.comp (isWeakHomotopyEquivalence_of_homotopyEquiv
      d.firstEndOverlapSourceHomeomorph.toHomotopyEquiv))

/-- On the intersection the map is the supplied actual local bridge SDR,
not a restriction of an arbitrarily weak map. -/
theorem firstEnd_restriction_intersection_weak (hV : IsOpen V)
    (R : TopCat.CylinderStrongDeformationRetract (d.bridgeEndCollarEnd h hi cut hc)) :
    IsWeakHomotopyEquivalence (restriction d.firstEnd.hom
      (d.firstEndCollarSet h hi cut ∩ d.firstBase ⁻¹' V)) := by
  have heq : (d.firstEndIntersectionTargetHomeomorph h hi cut hV).toHomotopyEquiv.toFun.comp
      ((d.bridgeEndCollarEnd h hi cut hc).hom.comp
        (d.firstEndIntersectionSourceHomeomorph h hi cut hc).toHomotopyEquiv.toFun) =
      restriction d.firstEnd.hom (d.firstEndCollarSet h hi cut ∩ d.firstBase ⁻¹' V) := by
    apply ContinuousMap.ext
    intro e
    exact Subtype.ext (ConcreteCategory.congr_hom d.first_isPushout.w
      (d.firstEndIntersectionSourceHomeomorph h hi cut hc e))
  rw [← heq]
  exact (isWeakHomotopyEquivalence_of_homotopyEquiv
    (d.firstEndIntersectionTargetHomeomorph h hi cut hV).toHomotopyEquiv).comp
      ((isWeakHomotopyEquivalence_of_homotopyEquiv R.toHomotopyEquiv).comp
        (isWeakHomotopyEquivalence_of_homotopyEquiv
          (d.firstEndIntersectionSourceHomeomorph h hi cut hc).toHomotopyEquiv))

/-- The unchanged first attachment preserves ordinary weakness of its original
bridge end. Its complete overlap condition is discharged by the genuine collar. -/
theorem firstEnd_isWeakHomotopyEquivalence (hV : IsOpen V)
    (R : TopCat.CylinderStrongDeformationRetract (d.bridgeEndCollarEnd h hi cut hc))
    (hweak : IsWeakHomotopyEquivalence d.i0.hom) :
    IsWeakHomotopyEquivalence d.firstEnd.hom :=
  isWeakHomotopyEquivalence_of_two_open d.firstEnd.hom
    (d.firstEndCollarSet h hi cut) (d.firstBase ⁻¹' V)
    (d.firstEndCollar_isOpen h hi cut) (hV.preimage d.firstBase.hom.continuous)
    (d.firstEndCollar_cover h hi cut hc)
    (d.firstEnd_restriction_collar_weak h hi cut hc R)
    (d.firstEnd_restriction_overlap_weak hV hweak)
    (d.firstEnd_restriction_intersection_weak h hi cut hc hV R)

end TopCat.OpenGluing.Data
