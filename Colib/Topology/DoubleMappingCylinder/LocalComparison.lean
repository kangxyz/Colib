/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DoubleMappingCylinder.Invariance
public import Colib.Topology.DoubleMappingCylinder.Collars
public import Colib.Topology.HomotopyPullback.RetractionBaseChange

/-!
# Canonical local comparisons for a map of double cylinders

A strict map of spans preserves height, restricts to equal-cutoff open
collars, and commutes with their endpoint retractions. Consequently the
canonical map from a source collar to the genuine pullback of the endpoint
map over the target collar retraction is an ordinary homotopy equivalence.
No fibration assumption on the endpoint maps is required.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/LocalComparison.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and proofs
with native namespace and import ownership. -/
@[expose] public section

open Topology

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.DoubleCylinder

variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')

/-- The canonical double-cylinder map preserves the actual height. -/
@[simp] theorem height_map (x : D) :
    height f' g' sq' (map sq sq' a b c wf wg x) = height f g sq x := by
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) x with
    ⟨⟨y, t⟩, h⟩ | ⟨y | z, h⟩
  · change l (y, t) = x at h
    rw [← h, map_cylinder_apply, height_cylinder, height_cylinder]
  · change e (Sum.inl y) = x at h
    rw [← h, map_left, height_left, height_left]
  · change e (Sum.inr z) = x at h
    rw [← h, map_right, height_right, height_right]

variable (cut : I)

@[simp] theorem preimage_leftCollarSet :
    map sq sq' a b c wf wg ⁻¹' leftCollarSet f' g' sq' cut =
      leftCollarSet f g sq cut := by
  ext x
  simp only [Set.mem_preimage, leftCollarSet, Set.mem_ofPred_eq, height_map]

@[simp] theorem preimage_rightCollarSet :
    map sq sq' a b c wf wg ⁻¹' rightCollarSet f' g' sq' cut =
      rightCollarSet f g sq cut := by
  ext x
  simp only [Set.mem_preimage, rightCollarSet, Set.mem_ofPred_eq, height_map]

/-- Restriction of the canonical map to equal-cutoff left collars. -/
def leftCollarMap : LeftCollar f g sq cut ⟶ LeftCollar f' g' sq' cut :=
  TopCat.ofHom ⟨fun x ↦ ⟨map sq sq' a b c wf wg x.1, by
    change height f' g' sq' (map sq sq' a b c wf wg x.1) < cut
    rw [height_map]
    exact x.2⟩, by fun_prop⟩

/-- Restriction of the canonical map to equal-cutoff right collars. -/
def rightCollarMap : RightCollar f g sq cut ⟶ RightCollar f' g' sq' cut :=
  TopCat.ofHom ⟨fun x ↦ ⟨map sq sq' a b c wf wg x.1, by
    change cut < height f' g' sq' (map sq sq' a b c wf wg x.1)
    rw [height_map]
    exact x.2⟩, by fun_prop⟩

@[simp] theorem leftCollarMap_val (x : LeftCollar f g sq cut) :
    (leftCollarMap sq sq' a b c wf wg cut x).1 = map sq sq' a b c wf wg x.1 := rfl

@[simp] theorem rightCollarMap_val (x : RightCollar f g sq cut) :
    (rightCollarMap sq sq' a b c wf wg cut x).1 = map sq sq' a b c wf wg x.1 := rfl

/-- The literal cylinder-coordinate map between restricted left cylinders. -/
def leftCollarCylinderMap :
    LeftCollarCylinder f g sq cut ⟶ LeftCollarCylinder f' g' sq' cut :=
  TopCat.ofHom ⟨fun z ↦ ⟨(a z.1.1, z.1.2), by
    have hz := z.2
    change height f g sq (l (z.1.1, z.1.2)) < cut at hz
    change height f' g' sq' (l' (a z.1.1, z.1.2)) < cut
    simpa only [height_cylinder] using hz⟩, by fun_prop⟩

/-- The literal cylinder-coordinate map between restricted right cylinders. -/
def rightCollarCylinderMap :
    RightCollarCylinder f g sq cut ⟶ RightCollarCylinder f' g' sq' cut :=
  TopCat.ofHom ⟨fun z ↦ ⟨(a z.1.1, z.1.2), by
    have hz := z.2
    change cut < height f g sq (l (z.1.1, z.1.2)) at hz
    change cut < height f' g' sq' (l' (a z.1.1, z.1.2))
    simpa only [height_cylinder] using hz⟩, by fun_prop⟩

@[simp] theorem leftCollarMap_cylinder (z : LeftCollarCylinder f g sq cut) :
    leftCollarMap sq sq' a b c wf wg cut (leftCollarCylinderInclusion f g sq cut z) =
      leftCollarCylinderInclusion f' g' sq' cut (leftCollarCylinderMap sq sq' a cut z) := by
  apply Subtype.ext
  exact map_cylinder_apply sq sq' a b c wf wg z.1.1 z.1.2

@[simp] theorem rightCollarMap_cylinder (z : RightCollarCylinder f g sq cut) :
    rightCollarMap sq sq' a b c wf wg cut (rightCollarCylinderInclusion f g sq cut z) =
      rightCollarCylinderInclusion f' g' sq' cut (rightCollarCylinderMap sq sq' a cut z) := by
  apply Subtype.ext
  exact map_cylinder_apply sq sq' a b c wf wg z.1.1 z.1.2

@[simp] theorem leftCollarMap_end (hcut : 0 < cut) (x : B) :
    leftCollarMap sq sq' a b c wf wg cut (leftCollarInclusion f g sq cut hcut x) =
      leftCollarInclusion f' g' sq' cut hcut (b x) := by
  apply Subtype.ext
  exact map_left sq sq' a b c wf wg x

@[simp] theorem rightCollarMap_end (hcut : cut < 1) (x : C) :
    rightCollarMap sq sq' a b c wf wg cut (rightCollarInclusion f g sq cut hcut x) =
      rightCollarInclusion f' g' sq' cut hcut (c x) := by
  apply Subtype.ext
  exact map_right sq sq' a b c wf wg x

/-- The left collar retractions commute with the canonical map. -/
theorem leftCollarProjection_naturality (hcut : 0 < cut) :
    leftCollarMap sq sq' a b c wf wg cut ≫ leftCollarProjection f' g' sq' cut hcut =
      leftCollarProjection f g sq cut hcut ≫ b := by
  apply ConcreteCategory.hom_ext
  intro x
  rcases Types.eq_or_eq_of_isPushout
    ((leftCollar_isPushout f g sq cut hcut).map (forget TopCat)) x with ⟨z, hz⟩ | ⟨y, hy⟩
  · change leftCollarCylinderInclusion f g sq cut z = x at hz
    subst x
    change leftCollarProjection f' g' sq' cut hcut
      (leftCollarMap sq sq' a b c wf wg cut (leftCollarCylinderInclusion f g sq cut z)) =
      b (leftCollarProjection f g sq cut hcut (leftCollarCylinderInclusion f g sq cut z))
    rw [leftCollarMap_cylinder, leftCollarProjection_cylinder, leftCollarProjection_cylinder]
    exact (ConcreteCategory.congr_hom wf z.1.1).symm
  · change leftCollarInclusion f g sq cut hcut y = x at hy
    subst x
    change leftCollarProjection f' g' sq' cut hcut
      (leftCollarMap sq sq' a b c wf wg cut (leftCollarInclusion f g sq cut hcut y)) =
      b (leftCollarProjection f g sq cut hcut (leftCollarInclusion f g sq cut hcut y))
    rw [leftCollarMap_end, leftCollarProjection_end, leftCollarProjection_end]

/-- The right collar retractions commute with the canonical map. -/
theorem rightCollarProjection_naturality (hcut : cut < 1) :
    rightCollarMap sq sq' a b c wf wg cut ≫ rightCollarProjection f' g' sq' cut hcut =
      rightCollarProjection f g sq cut hcut ≫ c := by
  apply ConcreteCategory.hom_ext
  intro x
  rcases Types.eq_or_eq_of_isPushout
    ((rightCollar_isPushout f g sq cut hcut).map (forget TopCat)) x with ⟨z, hz⟩ | ⟨y, hy⟩
  · change rightCollarCylinderInclusion f g sq cut z = x at hz
    subst x
    change rightCollarProjection f' g' sq' cut hcut
      (rightCollarMap sq sq' a b c wf wg cut (rightCollarCylinderInclusion f g sq cut z)) =
      c (rightCollarProjection f g sq cut hcut (rightCollarCylinderInclusion f g sq cut z))
    rw [rightCollarMap_cylinder, rightCollarProjection_cylinder, rightCollarProjection_cylinder]
    exact (ConcreteCategory.congr_hom wg z.1.1).symm
  · change rightCollarInclusion f g sq cut hcut y = x at hy
    subst x
    change rightCollarProjection f' g' sq' cut hcut
      (rightCollarMap sq sq' a b c wf wg cut (rightCollarInclusion f g sq cut hcut y)) =
      c (rightCollarProjection f g sq cut hcut (rightCollarInclusion f g sq cut hcut y))
    rw [rightCollarMap_end, rightCollarProjection_end, rightCollarProjection_end]

/-- The left collar contraction stays in fibers of its own retraction. -/
theorem leftCollarDeformation_projection (hcut : 0 < cut) :
    (leftCollarStrongDeformationRetract f g sq cut hcut).H ≫
        leftCollarProjection f g sq cut hcut =
      fst (LeftCollar f g sq cut) TopCat.I ≫ leftCollarProjection f g sq cut hcut :=
  leftCollarDeformation_over_collar f g sq cut hcut
    (leftCollarProjection f g sq cut hcut) f
    (leftCollarProjection_cylinder f g sq cut hcut)

/-- The right collar contraction stays in fibers of its own retraction. -/
theorem rightCollarDeformation_projection (hcut : cut < 1) :
    (rightCollarStrongDeformationRetract f g sq cut hcut).H ≫
        rightCollarProjection f g sq cut hcut =
      fst (RightCollar f g sq cut) TopCat.I ≫ rightCollarProjection f g sq cut hcut :=
  rightCollarDeformation_over_collar f g sq cut hcut
    (rightCollarProjection f g sq cut hcut) g
    (rightCollarProjection_cylinder f g sq cut hcut)

/-- The genuine strict pullback of the left endpoint map over the target
left collar projection. -/
abbrev LeftCollarPullback (hcut : 0 < cut) : TopCat.{u} :=
  TopCat.of (RetractionPullback.Space
    (leftCollarStrongDeformationRetract f' g' sq' cut hcut) b)

/-- The genuine strict pullback of the right endpoint map over the target
right collar projection. -/
abbrev RightCollarPullback (hcut : cut < 1) : TopCat.{u} :=
  TopCat.of (RetractionPullback.Space
    (rightCollarStrongDeformationRetract f' g' sq' cut hcut) c)

/-- The actual local comparison sends a source left-collar point to its
image in the target collar and its source endpoint retraction. -/
def leftCollarComparison (hcut : 0 < cut) :
    LeftCollar f g sq cut ⟶ LeftCollarPullback sq' b cut hcut :=
  RetractionPullback.comparison
    (leftCollarStrongDeformationRetract f' g' sq' cut hcut) b
    (leftCollarStrongDeformationRetract f g sq cut hcut)
    (leftCollarMap sq sq' a b c wf wg cut)
    (leftCollarProjection_naturality sq sq' a b c wf wg cut hcut)

/-- The actual local comparison for the right collar. -/
def rightCollarComparison (hcut : cut < 1) :
    RightCollar f g sq cut ⟶ RightCollarPullback sq' c cut hcut :=
  RetractionPullback.comparison
    (rightCollarStrongDeformationRetract f' g' sq' cut hcut) c
    (rightCollarStrongDeformationRetract f g sq cut hcut)
    (rightCollarMap sq sq' a b c wf wg cut)
    (rightCollarProjection_naturality sq sq' a b c wf wg cut hcut)

@[simp] theorem leftCollarComparison_fst (hcut : 0 < cut) (x : LeftCollar f g sq cut) :
    (leftCollarComparison sq sq' a b c wf wg cut hcut x).1.1 =
      leftCollarMap sq sq' a b c wf wg cut x := rfl

@[simp] theorem leftCollarComparison_snd (hcut : 0 < cut) (x : LeftCollar f g sq cut) :
    (leftCollarComparison sq sq' a b c wf wg cut hcut x).1.2 =
      leftCollarProjection f g sq cut hcut x := rfl

@[simp] theorem rightCollarComparison_fst (hcut : cut < 1) (x : RightCollar f g sq cut) :
    (rightCollarComparison sq sq' a b c wf wg cut hcut x).1.1 =
      rightCollarMap sq sq' a b c wf wg cut x := rfl

@[simp] theorem rightCollarComparison_snd (hcut : cut < 1) (x : RightCollar f g sq cut) :
    (rightCollarComparison sq sq' a b c wf wg cut hcut x).1.2 =
      rightCollarProjection f g sq cut hcut x := rfl

/-- Exact cylinder-coordinate formula for the left local comparison. -/
@[simp] theorem leftCollarComparison_cylinder (hcut : 0 < cut)
    (z : LeftCollarCylinder f g sq cut) :
    (leftCollarComparison sq sq' a b c wf wg cut hcut
      (leftCollarCylinderInclusion f g sq cut z)).1 =
      (leftCollarCylinderInclusion f' g' sq' cut
        (leftCollarCylinderMap sq sq' a cut z), f z.1.1) := by
  apply Prod.ext
  · exact leftCollarMap_cylinder sq sq' a b c wf wg cut z
  · exact leftCollarProjection_cylinder f g sq cut hcut z

/-- Exact cylinder-coordinate formula for the right local comparison. -/
@[simp] theorem rightCollarComparison_cylinder (hcut : cut < 1)
    (z : RightCollarCylinder f g sq cut) :
    (rightCollarComparison sq sq' a b c wf wg cut hcut
      (rightCollarCylinderInclusion f g sq cut z)).1 =
      (rightCollarCylinderInclusion f' g' sq' cut
        (rightCollarCylinderMap sq sq' a cut z), g z.1.1) := by
  apply Prod.ext
  · exact rightCollarMap_cylinder sq sq' a b c wf wg cut z
  · exact rightCollarProjection_cylinder f g sq cut hcut z

@[simp] theorem leftCollarComparison_end (hcut : 0 < cut) (x : B) :
    leftCollarComparison sq sq' a b c wf wg cut hcut
        (leftCollarInclusion f g sq cut hcut x) =
      RetractionPullback.inclusion
        (leftCollarStrongDeformationRetract f' g' sq' cut hcut) b x := by
  apply Subtype.ext
  exact Prod.ext (leftCollarMap_end sq sq' a b c wf wg cut hcut x)
    (leftCollarProjection_end f g sq cut hcut x)

@[simp] theorem rightCollarComparison_end (hcut : cut < 1) (x : C) :
    rightCollarComparison sq sq' a b c wf wg cut hcut
        (rightCollarInclusion f g sq cut hcut x) =
      RetractionPullback.inclusion
        (rightCollarStrongDeformationRetract f' g' sq' cut hcut) c x := by
  apply Subtype.ext
  exact Prod.ext (rightCollarMap_end sq sq' a b c wf wg cut hcut x)
    (rightCollarProjection_end f g sq cut hcut x)

/-- The canonical left local comparison itself is an ordinary homotopy
equivalence into the genuine strict pullback. -/
def leftCollarComparisonHomotopyEquiv (hcut : 0 < cut) :
    ContinuousMap.HomotopyEquiv (LeftCollar f g sq cut) (LeftCollarPullback sq' b cut hcut) :=
  RetractionPullback.comparisonHomotopyEquiv
    (leftCollarStrongDeformationRetract f' g' sq' cut hcut) b
    (leftCollarDeformation_projection sq' cut hcut)
    (leftCollarStrongDeformationRetract f g sq cut hcut)
    (leftCollarMap sq sq' a b c wf wg cut)
    (leftCollarProjection_naturality sq sq' a b c wf wg cut hcut)
    (by
      apply ConcreteCategory.hom_ext
      exact leftCollarMap_end sq sq' a b c wf wg cut hcut)

/-- The canonical right local comparison itself is an ordinary homotopy
equivalence into the genuine strict pullback. -/
def rightCollarComparisonHomotopyEquiv (hcut : cut < 1) :
    ContinuousMap.HomotopyEquiv (RightCollar f g sq cut) (RightCollarPullback sq' c cut hcut) :=
  RetractionPullback.comparisonHomotopyEquiv
    (rightCollarStrongDeformationRetract f' g' sq' cut hcut) c
    (rightCollarDeformation_projection sq' cut hcut)
    (rightCollarStrongDeformationRetract f g sq cut hcut)
    (rightCollarMap sq sq' a b c wf wg cut)
    (rightCollarProjection_naturality sq sq' a b c wf wg cut hcut)
    (by
      apply ConcreteCategory.hom_ext
      exact rightCollarMap_end sq sq' a b c wf wg cut hcut)

@[simp] theorem leftCollarComparisonHomotopyEquiv_toFun (hcut : 0 < cut) :
    (leftCollarComparisonHomotopyEquiv sq sq' a b c wf wg cut hcut).toFun =
      (leftCollarComparison sq sq' a b c wf wg cut hcut).hom := rfl

@[simp] theorem rightCollarComparisonHomotopyEquiv_toFun (hcut : cut < 1) :
    (rightCollarComparisonHomotopyEquiv sq sq' a b c wf wg cut hcut).toFun =
      (rightCollarComparison sq sq' a b c wf wg cut hcut).hom := rfl

/-- The source left collar is literally the preimage of the target left
collar, with the subspace topology used in a local pullback argument. -/
def leftCollarPreimageHomeomorph : LeftCollar f g sq cut ≃ₜ
    {x : D // map sq sq' a b c wf wg x ∈ leftCollarSet f' g' sq' cut} :=
  Homeomorph.setCongr (preimage_leftCollarSet sq sq' a b c wf wg cut).symm

/-- The corresponding literal preimage identification for right collars. -/
def rightCollarPreimageHomeomorph : RightCollar f g sq cut ≃ₜ
    {x : D // map sq sq' a b c wf wg x ∈ rightCollarSet f' g' sq' cut} :=
  Homeomorph.setCongr (preimage_rightCollarSet sq sq' a b c wf wg cut).symm

@[simp] theorem leftCollarPreimageHomeomorph_val (x : LeftCollar f g sq cut) :
    (leftCollarPreimageHomeomorph sq sq' a b c wf wg cut x).1 = x.1 := rfl

@[simp] theorem rightCollarPreimageHomeomorph_val (x : RightCollar f g sq cut) :
    (rightCollarPreimageHomeomorph sq sq' a b c wf wg cut x).1 = x.1 := rfl

end TopCat.DoubleCylinder
