/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.OpenCover.TwoSet.Partition
public import Colib.Topology.DoubleMappingCylinder.Invariance

/-!
# Homotopy equivalences detected on a partitioned two-open cover

The inverse image of a two-open partition provides a genuine cover of the
source. Homotopy equivalences on the two charts and their intersection
induce an equivalence of their actual double cylinders. The two canonical
collapse equivalences then recover the original map, with that map as the
exact forward continuous map.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/OpenCover/TwoSet/CylinderInvariance.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and proofs
with native namespace and import ownership. -/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.TwoOpenPartition
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pull back all the open sets and the actual cutoff of a two-open partition. -/
def pullback (P : TwoOpenPartition Y) (p : C(X, Y)) : TwoOpenPartition X where
  leftSet := p ⁻¹' P.leftSet
  rightSet := p ⁻¹' P.rightSet
  left_open := P.left_open.preimage p.continuous
  right_open := P.right_open.preimage p.continuous
  cover := by rw [← Set.preimage_union, P.cover, Set.preimage_univ]
  cutoff := P.cutoff.comp p
  zeroSet := p ⁻¹' P.zeroSet
  oneSet := p ⁻¹' P.oneSet
  zero_open := P.zero_open.preimage p.continuous
  one_open := P.one_open.preimage p.continuous
  right_zero_cover := by rw [← Set.preimage_union, P.right_zero_cover, Set.preimage_univ]
  left_one_cover := by rw [← Set.preimage_union, P.left_one_cover, Set.preimage_univ]
  cutoff_zero := fun x hx ↦ P.cutoff_zero (p x) hx
  cutoff_one := fun x hx ↦ P.cutoff_one (p x) hx

/-- The inclusion of the overlap in the left chart. -/
def leftLeg (P : TwoOpenPartition X) : TopCat.of P.Overlap ⟶ TopCat.of P.Left :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1, x.2.1⟩, by fun_prop⟩

/-- The inclusion of the overlap in the right chart. -/
def rightLeg (P : TwoOpenPartition X) : TopCat.of P.Overlap ⟶ TopCat.of P.Right :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1, x.2.2⟩, by fun_prop⟩

/-- A chosen ordinary double cylinder of the actual open-cover span. -/
abbrev CoverCylinder (P : TwoOpenPartition X) : TopCat.{u} :=
  pushout (TopCat.intervalEndpoints (TopCat.of P.Overlap)) P.endMap

/-- The canonical map of the cover overlap times `I` into the double mapping cylinder of a
two-open partition. -/
abbrev coverLine (P : TwoOpenPartition X) : TopCat.of P.Overlap ⊗ TopCat.I ⟶ P.CoverCylinder :=
  pushout.inl _ _
/-- The canonical map of the two open charts into the double mapping cylinder of the partition. -/
abbrev coverEnds (P : TwoOpenPartition X) : TopCat.of (P.Left ⊕ P.Right) ⟶ P.CoverCylinder :=
  pushout.inr _ _

/-- The chosen cover cylinder has the genuine pushout universal property. -/
theorem coverCylinderSquare (P : TwoOpenPartition X) :
    IsPushout (TopCat.intervalEndpoints (TopCat.of P.Overlap))
      (DoubleCylinder.endMap P.leftLeg P.rightLeg) P.coverLine P.coverEnds :=
  IsPushout.of_hasPushout _ _

variable (P : TwoOpenPartition Y) (p : C(X, Y))

/-- The canonical map on the inverse-image left chart. -/
def leftRestriction : C((P.pullback p).Left, P.Left) :=
  ⟨fun x ↦ ⟨p x.1, x.2⟩, by fun_prop⟩

/-- The canonical map on the inverse-image right chart. -/
def rightRestriction : C((P.pullback p).Right, P.Right) :=
  ⟨fun x ↦ ⟨p x.1, x.2⟩, by fun_prop⟩

/-- The canonical map on the actual overlap of the inverse-image charts. -/
def overlapRestriction : C((P.pullback p).Overlap, P.Overlap) :=
  ⟨fun x ↦ ⟨p x.1, x.2⟩, by fun_prop⟩

/-- The induced map of the two actual cover double cylinders. -/
abbrev coverCylinderMap : (P.pullback p).CoverCylinder ⟶ P.CoverCylinder :=
  DoubleCylinder.map (P.pullback p).coverCylinderSquare P.coverCylinderSquare
    (TopCat.ofHom (P.overlapRestriction p)) (TopCat.ofHom (P.leftRestriction p))
    (TopCat.ofHom (P.rightRestriction p)) rfl rfl

/-- Cover-cylinder maps commute exactly with the collapse to the covered spaces. -/
theorem coverCylinderMap_collapse :
    P.coverCylinderMap p ≫ P.collapse P.coverCylinderSquare =
      (P.pullback p).collapse (P.pullback p).coverCylinderSquare ≫ TopCat.ofHom p := by
  apply (P.pullback p).coverCylinderSquare.hom_ext
  · apply ConcreteCategory.hom_ext
    rintro ⟨x, ⟨t⟩⟩
    change P.collapse P.coverCylinderSquare
      (P.coverCylinderMap p ((P.pullback p).coverLine (x, ULift.up t))) =
      p ((P.pullback p).collapse (P.pullback p).coverCylinderSquare
        ((P.pullback p).coverLine (x, ULift.up t)))
    rw [DoubleCylinder.map_cylinder_apply, collapse_cylinder, collapse_cylinder]
    rfl
  · apply ConcreteCategory.hom_ext
    rintro (x | x)
    · change P.collapse P.coverCylinderSquare
        (P.coverCylinderMap p ((P.pullback p).coverEnds (Sum.inl x))) =
        p ((P.pullback p).collapse (P.pullback p).coverCylinderSquare
          ((P.pullback p).coverEnds (Sum.inl x)))
      rw [DoubleCylinder.map_left, collapse_left, collapse_left]
      rfl
    · change P.collapse P.coverCylinderSquare
        (P.coverCylinderMap p ((P.pullback p).coverEnds (Sum.inr x))) =
        p ((P.pullback p).collapse (P.pullback p).coverCylinderSquare
          ((P.pullback p).coverEnds (Sum.inr x)))
      rw [DoubleCylinder.map_right, collapse_right, collapse_right]
      rfl

/-- Ordinary homotopy equivalences on a partitioned two-open cover and its
intersection imply an ordinary homotopy equivalence of the original map.
The forward map is exactly the prescribed map, without coherence assumptions
on the three chosen homotopy inverses. -/
def homotopyEquivOfRestrictions
    (eL : ContinuousMap.HomotopyEquiv (P.pullback p).Left P.Left)
    (hL : eL.toFun = P.leftRestriction p)
    (eR : ContinuousMap.HomotopyEquiv (P.pullback p).Right P.Right)
    (hR : eR.toFun = P.rightRestriction p)
    (eO : ContinuousMap.HomotopyEquiv (P.pullback p).Overlap P.Overlap)
    (hO : eO.toFun = P.overlapRestriction p) : ContinuousMap.HomotopyEquiv X Y := by
  let E := ((P.pullback p).collapseHomotopyEquiv
    (P.pullback p).coverCylinderSquare).symm.trans
      ((DoubleCylinder.mapHomotopyEquiv (P.pullback p).coverCylinderSquare
        P.coverCylinderSquare (TopCat.ofHom (P.overlapRestriction p))
        (TopCat.ofHom (P.leftRestriction p)) (TopCat.ofHom (P.rightRestriction p))
        rfl rfl eO hO eL hL eR hR).trans
        (P.collapseHomotopyEquiv P.coverCylinderSquare))
  have hE : E.toFun = p := by
    ext x
    change P.collapse P.coverCylinderSquare
      (P.coverCylinderMap p ((P.pullback p).sectionMap
        (P.pullback p).coverCylinderSquare x)) = p x
    exact (ConcreteCategory.congr_hom (P.coverCylinderMap_collapse p) _).trans
      (congrArg p ((P.pullback p).collapse_sectionMap (P.pullback p).coverCylinderSquare x))
  exact { E with
    toFun := p
    left_inv := by simpa only [hE] using E.left_inv
    right_inv := by simpa only [hE] using E.right_inv }

@[simp] theorem homotopyEquivOfRestrictions_toFun
    (eL : ContinuousMap.HomotopyEquiv (P.pullback p).Left P.Left)
    (hL : eL.toFun = P.leftRestriction p)
    (eR : ContinuousMap.HomotopyEquiv (P.pullback p).Right P.Right)
    (hR : eR.toFun = P.rightRestriction p)
    (eO : ContinuousMap.HomotopyEquiv (P.pullback p).Overlap P.Overlap)
    (hO : eO.toFun = P.overlapRestriction p) :
    (P.homotopyEquivOfRestrictions p eL hL eR hR eO hO).toFun = p := rfl

end TopCat.TwoOpenPartition
