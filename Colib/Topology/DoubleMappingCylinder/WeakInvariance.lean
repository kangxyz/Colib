/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DoubleMappingCylinder.LocalComparison
public import Colib.Topology.DoubleMappingCylinder.Band
public import Colib.Topology.Homotopy.HomotopyGroup.ProductWeakEquivalence
public import Colib.Topology.Homotopy.HomotopyGroup.WeakLocality

/-!
# Objectwise weak invariance of the original double-cylinder map

The actual left and right open collars retract to their original endpoints;
their overlap is the actual attaching-space product with its height band.
Ordinary two-open weak locality proves that three original weak maps induce
a weak map of the original double cylinders. Spaces and attaching maps are
arbitrary, and no continuous inverse for a weak map is used.


Implementation provenance:
`Quillen/Topology/DoubleMappingCylinder/WeakInvariance.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology.CubicalSubdivision


noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
namespace TopCat.DoubleCylinder
open CubicalSubdivision
variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')

/-- The original left collar map is weak whenever its original endpoint map
is weak. Both actual collar-end inclusions are genuine SDRs. -/
theorem leftCollarMap_isWeakHomotopyEquivalence
    (cut : I) (hcut : 0 < cut) (hb : IsWeakHomotopyEquivalence b.hom) :
    IsWeakHomotopyEquivalence (leftCollarMap sq sq' a b c wf wg cut).hom := by
  have he : (leftCollarMap sq sq' a b c wf wg cut).hom.comp
      (leftCollarInclusion f g sq cut hcut).hom =
      (leftCollarInclusion f' g' sq' cut hcut).hom.comp b.hom := by
    ext x
    exact leftCollarMap_end sq sq' a b c wf wg cut hcut x
  have hw := (isWeakHomotopyEquivalence_of_homotopyEquiv
    (leftCollarStrongDeformationRetract f' g' sq' cut hcut).toHomotopyEquiv).comp hb
  change IsWeakHomotopyEquivalence ((leftCollarInclusion f' g' sq' cut hcut).hom.comp b.hom) at hw
  rw [← he] at hw
  exact hw.of_comp_left (isWeakHomotopyEquivalence_of_homotopyEquiv
    (leftCollarStrongDeformationRetract f g sq cut hcut).toHomotopyEquiv)

/-- The matching actual right collar map inherits original endpoint weakness. -/
theorem rightCollarMap_isWeakHomotopyEquivalence
    (cut : I) (hcut : cut < 1) (hc : IsWeakHomotopyEquivalence c.hom) :
    IsWeakHomotopyEquivalence (rightCollarMap sq sq' a b c wf wg cut).hom := by
  have he : (rightCollarMap sq sq' a b c wf wg cut).hom.comp
      (rightCollarInclusion f g sq cut hcut).hom =
      (rightCollarInclusion f' g' sq' cut hcut).hom.comp c.hom := by
    ext x
    exact rightCollarMap_end sq sq' a b c wf wg cut hcut x
  have hw := (isWeakHomotopyEquivalence_of_homotopyEquiv
    (rightCollarStrongDeformationRetract f' g' sq' cut hcut).toHomotopyEquiv).comp hc
  change IsWeakHomotopyEquivalence ((rightCollarInclusion f' g' sq' cut hcut).hom.comp c.hom) at hw
  rw [← he] at hw
  exact hw.of_comp_left (isWeakHomotopyEquivalence_of_homotopyEquiv
    (rightCollarStrongDeformationRetract f g sq cut hcut).toHomotopyEquiv)

/-- The literal pullback restriction to the target left collar is weak. -/
theorem leftCollarRestriction_isWeakHomotopyEquivalence
    (cut : I) (hcut : 0 < cut) (hb : IsWeakHomotopyEquivalence b.hom) :
    IsWeakHomotopyEquivalence
      (restriction (map sq sq' a b c wf wg).hom (leftCollarSet f' g' sq' cut)) := by
  let e := leftCollarPreimageHomeomorph sq sq' a b c wf wg cut
  have hw : IsWeakHomotopyEquivalence
      ((restriction (map sq sq' a b c wf wg).hom (leftCollarSet f' g' sq' cut)).comp
        e.toHomotopyEquiv.toFun) :=
    leftCollarMap_isWeakHomotopyEquivalence sq sq' a b c wf wg cut hcut hb
  exact hw.of_comp_left (isWeakHomotopyEquivalence_of_homotopyEquiv e.toHomotopyEquiv)

/-- The literal target right-collar restriction is weak from its endpoint. -/
theorem rightCollarRestriction_isWeakHomotopyEquivalence
    (cut : I) (hcut : cut < 1) (hc : IsWeakHomotopyEquivalence c.hom) :
    IsWeakHomotopyEquivalence
      (restriction (map sq sq' a b c wf wg).hom (rightCollarSet f' g' sq' cut)) := by
  let e := rightCollarPreimageHomeomorph sq sq' a b c wf wg cut
  have hw : IsWeakHomotopyEquivalence
      ((restriction (map sq sq' a b c wf wg).hom (rightCollarSet f' g' sq' cut)).comp
        e.toHomotopyEquiv.toFun) :=
    rightCollarMap_isWeakHomotopyEquivalence sq sq' a b c wf wg cut hcut hc
  exact hw.of_comp_left (isWeakHomotopyEquivalence_of_homotopyEquiv e.toHomotopyEquiv)

/-- The overlap chart has the same original point and full band parameter;
only the order of the two collar membership proofs is exchanged. -/
def overlapBandHomeomorph (lo hi : I) : A × Band lo hi ≃ₜ
    (leftCollarSet f g sq hi ∩ rightCollarSet f g sq lo : Set D) :=
  (bandHomeomorph f g sq lo hi).trans {
    toFun z := ⟨z.val,z.property.2,z.property.1⟩
    invFun z := ⟨z.val,z.property.2,z.property.1⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

@[simp] theorem overlapBandHomeomorph_val (lo hi : I) (z : A × Band lo hi) :
    (overlapBandHomeomorph sq lo hi z).val = l (z.1,ULift.up z.2.val) := rfl

/-- Height preservation identifies the actual source overlap with the literal
preimage of the target overlap. -/
def overlapPreimageHomeomorph (lo hi : I) :
    (leftCollarSet f g sq hi ∩ rightCollarSet f g sq lo : Set D) ≃ₜ
      {x : D // map sq sq' a b c wf wg x ∈
        leftCollarSet f' g' sq' hi ∩ rightCollarSet f' g' sq' lo} :=
  Homeomorph.setCongr (by
    ext x
    change (height f g sq x < hi ∧ lo < height f g sq x) ↔
      (height f' g' sq' (map sq sq' a b c wf wg x) < hi ∧
        lo < height f' g' sq' (map sq sq' a b c wf wg x))
    rw [height_map])

/-- The literal overlap restriction is conjugate to the original attaching
map times the identity on the complete height-band parameter. -/
theorem overlapRestriction_isWeakHomotopyEquivalence
    (lo hi : I) (ha : IsWeakHomotopyEquivalence a.hom) :
    IsWeakHomotopyEquivalence (restriction (map sq sq' a b c wf wg).hom
      (leftCollarSet f' g' sq' hi ∩ rightCollarSet f' g' sq' lo)) := by
  let es := (overlapBandHomeomorph sq lo hi).trans
    (overlapPreimageHomeomorph sq sq' a b c wf wg lo hi)
  let et := overlapBandHomeomorph sq' lo hi
  have he : (restriction (map sq sq' a b c wf wg).hom
      (leftCollarSet f' g' sq' hi ∩ rightCollarSet f' g' sq' lo)).comp
        es.toHomotopyEquiv.toFun =
      et.toHomotopyEquiv.toFun.comp (a.hom.prodMap (ContinuousMap.id (Band lo hi))) := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    exact map_cylinder_apply sq sq' a b c wf wg z.1 (ULift.up z.2.val)
  have hw := (isWeakHomotopyEquivalence_of_homotopyEquiv et.toHomotopyEquiv).comp
    (ha.prodMap_id (Band lo hi))
  rw [← he] at hw
  exact hw.of_comp_left (isWeakHomotopyEquivalence_of_homotopyEquiv es.toHomotopyEquiv)

/-- Objectwise complete weak equivalences induce a complete weak equivalence
of the original double cylinders. No HEP, lifting or separation condition is
required on these arbitrary spaces. -/
theorem map_isWeakHomotopyEquivalence
    (ha : IsWeakHomotopyEquivalence a.hom) (hb : IsWeakHomotopyEquivalence b.hom)
    (hc : IsWeakHomotopyEquivalence c.hom) :
    IsWeakHomotopyEquivalence (map sq sq' a b c wf wg).hom := by
  let lo : I := ⟨1 / 4,by norm_num⟩
  let hi : I := ⟨3 / 4,by norm_num⟩
  have hh : lo < hi := by change (1 / 4 : ℝ) < 3 / 4; norm_num
  have hh0 : 0 < hi := by change (0 : ℝ) < 3 / 4; norm_num
  have hl1 : lo < 1 := by change (1 / 4 : ℝ) < 1; norm_num
  exact isWeakHomotopyEquivalence_of_two_open (map sq sq' a b c wf wg).hom
    (leftCollarSet f' g' sq' hi) (rightCollarSet f' g' sq' lo)
    (leftCollar_isOpen f' g' sq' hi) (rightCollar_isOpen f' g' sq' lo)
    (collar_cover f' g' sq' hi lo hh)
    (leftCollarRestriction_isWeakHomotopyEquivalence sq sq' a b c wf wg hi hh0 hb)
    (rightCollarRestriction_isWeakHomotopyEquivalence sq sq' a b c wf wg lo hl1 hc)
    (overlapRestriction_isWeakHomotopyEquivalence sq sq' a b c wf wg lo hi ha)

end TopCat.DoubleCylinder
