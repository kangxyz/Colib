/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.BandContraction
public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.WeakSquare

/-!
# Finite overlap-to-collar connectivity from the original attaching maps

The actual overlap projection and collar retraction form a strictly commuting square with
the original attaching map. Both vertical maps are genuine homotopy equivalences. The proved
original weak-square map transfers each finite bound on actual fibers, including nonemptiness
and arbitrary basepoints. No independent connectivity premise on the overlap inclusion is used.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/CollarConnectivity.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace TopCat.DoubleCylinder

variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (lo hi : unitInterval)

/-- The literal inclusion of the open height overlap into the left collar. -/
def leftOverlapInclusion :
    C({z : LeftCollar f g sq hi // lo < height f g sq z.val}, LeftCollar f g sq hi) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The literal inclusion of the same open height overlap into the right collar. -/
def rightOverlapInclusion :
    C({z : RightCollar f g sq lo // height f g sq z.val < hi}, RightCollar f g sq lo) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The actual overlap-to-source projection, with its explicit band-point homotopy inverse. -/
def leftOverlapProjectionEquiv (c : Band lo hi) :
    ContinuousMap.HomotopyEquiv
      {z : LeftCollar f g sq hi // lo < height f g sq z.val} A :=
  (leftBandHomeomorph f g sq lo hi).symm.toHomotopyEquiv.trans
    (bandProjectionHomotopyEquiv lo hi A c)

/-- The same original source projection in the right overlap coordinates. -/
def rightOverlapProjectionEquiv (c : Band lo hi) :
    ContinuousMap.HomotopyEquiv
      {z : RightCollar f g sq lo // height f g sq z.val < hi} A :=
  (rightBandHomeomorph f g sq lo hi).symm.toHomotopyEquiv.trans
    (bandProjectionHomotopyEquiv lo hi A c)

/-- The original overlap projection and left collar retraction recover exactly f. -/
theorem leftOverlap_projection_square (c : Band lo hi) (hhi : 0 < hi) :
    (leftCollarProjection f g sq hi hhi).hom.comp (leftOverlapInclusion f g sq lo hi) =
      f.hom.comp (leftOverlapProjectionEquiv f g sq lo hi c).toFun := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨⟨x, t⟩, rfl⟩ := (leftBandHomeomorph f g sq lo hi).surjective z
  change leftCollarProjection f g sq hi hhi
      (leftBandHomeomorph f g sq lo hi (x, t)).val =
    f (((leftBandHomeomorph f g sq lo hi).symm
      (leftBandHomeomorph f g sq lo hi (x, t))).1)
  rw [Homeomorph.symm_apply_apply]
  exact leftCollarProjection_apply_cylinder f g sq hi hhi x (ULift.up t.val) t.property.2

/-- The original overlap projection and right collar retraction recover exactly g. -/
theorem rightOverlap_projection_square (c : Band lo hi) (hlo : lo < 1) :
    (rightCollarProjection f g sq lo hlo).hom.comp (rightOverlapInclusion f g sq lo hi) =
      g.hom.comp (rightOverlapProjectionEquiv f g sq lo hi c).toFun := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨⟨x, t⟩, rfl⟩ := (rightBandHomeomorph f g sq lo hi).surjective z
  change rightCollarProjection f g sq lo hlo
      (rightBandHomeomorph f g sq lo hi (x, t)).val =
    g (((rightBandHomeomorph f g sq lo hi).symm
      (rightBandHomeomorph f g sq lo hi (x, t))).1)
  rw [Homeomorph.symm_apply_apply]
  exact rightCollarProjection_apply_cylinder f g sq lo hlo x (ULift.up t.val) t.property.1

/-- The original left attaching-map bound proves the actual overlap inclusion's finite
connectivity at every fiber point, with genuine component coverage. -/
theorem leftOverlapInclusion_isHomotopyConnectedMap (c : Band lo hi) (n : ℕ)
    (hf : IsHomotopyConnectedMap f.hom n) :
    IsHomotopyConnectedMap (leftOverlapInclusion f g sq lo hi) n := by
  have hhi : 0 < hi := lt_of_le_of_lt (bot_le : 0 ≤ lo) (c.property.1.trans c.property.2)
  apply IsHomotopyConnectedMap.of_weak_square
    (leftOverlapProjectionEquiv f g sq lo hi c).toFun
    (leftCollarProjection f g sq hi hhi).hom
    (leftOverlap_projection_square f g sq lo hi c hhi)
    (isWeakHomotopyEquivalence_of_homotopyEquiv (leftOverlapProjectionEquiv f g sq lo hi c))
    (isWeakHomotopyEquivalence_of_homotopyEquiv
      (leftCollarStrongDeformationRetract f g sq hi hhi).toHomotopyEquiv.symm) n hf

/-- The matching bound on the actual right overlap inclusion comes from the original g. -/
theorem rightOverlapInclusion_isHomotopyConnectedMap (c : Band lo hi) (n : ℕ)
    (hg : IsHomotopyConnectedMap g.hom n) :
    IsHomotopyConnectedMap (rightOverlapInclusion f g sq lo hi) n := by
  have hlo : lo < 1 := lt_of_lt_of_le (c.property.1.trans c.property.2) (le_top : hi ≤ 1)
  apply IsHomotopyConnectedMap.of_weak_square
    (rightOverlapProjectionEquiv f g sq lo hi c).toFun
    (rightCollarProjection f g sq lo hlo).hom
    (rightOverlap_projection_square f g sq lo hi c hlo)
    (isWeakHomotopyEquivalence_of_homotopyEquiv (rightOverlapProjectionEquiv f g sq lo hi c))
    (isWeakHomotopyEquivalence_of_homotopyEquiv
      (rightCollarStrongDeformationRetract f g sq lo hlo).toHomotopyEquiv.symm) n hg

/-- Ordered actual collar cuts suffice for the left finite bound: the explicit midpoint
provides the contraction point, so no additional band-point hypothesis is required. -/
theorem leftOverlapInclusion_isHomotopyConnectedMap_of_lt (h : lo < hi) (n : ℕ)
    (hf : IsHomotopyConnectedMap f.hom n) :
    IsHomotopyConnectedMap (leftOverlapInclusion f g sq lo hi) n :=
  leftOverlapInclusion_isHomotopyConnectedMap f g sq lo hi (bandMidpoint lo hi h) n hf

/-- The same explicit midpoint removes the band-point premise from the right collar bound. -/
theorem rightOverlapInclusion_isHomotopyConnectedMap_of_lt (h : lo < hi) (n : ℕ)
    (hg : IsHomotopyConnectedMap g.hom n) :
    IsHomotopyConnectedMap (rightOverlapInclusion f g sq lo hi) n :=
  rightOverlapInclusion_isHomotopyConnectedMap f g sq lo hi (bandMidpoint lo hi h) n hg

end TopCat.DoubleCylinder
