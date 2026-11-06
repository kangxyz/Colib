/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.OpenGluing.FibrationSpan.DoubleCylinder
public import Colib.Topology.DoubleMappingCylinder.Band
public import Colib.Topology.DoubleMappingCylinder.LocalComparison

/-! The actual fibration-span normalization for a map of double cylinders.
The end spaces are genuine pullbacks over the two base collars and the
overlap maps are the original strict cartesian edge comparisons times the
actual height band. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/Finite/Basic.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and hypotheses. -/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.DoubleCylinder.FiniteNormalization

/-- The lower cut `1 / 4` in the unit interval used for the right height collar. -/
def lower : I := ⟨1 / 4, by norm_num⟩
/-- The upper cut `3 / 4` in the unit interval used for the left height collar. -/
def upper : I := ⟨3 / 4, by norm_num⟩
theorem lower_lt_one : lower < 1 := by change (1 / 4 : ℝ) < 1; norm_num
theorem zero_lt_upper : 0 < upper := by change (0 : ℝ) < 3 / 4; norm_num

variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')

/-- The left open collar of the target double cylinder, consisting of heights below `3 / 4`. -/
abbrev LeftSet := leftCollarSet f' g' sq' upper
/-- The right open collar of the target double cylinder, consisting of heights above `1 / 4`. -/
abbrev RightSet := rightCollarSet f' g' sq' lower
/-- The intersection of the target height collars, with heights strictly between `1 / 4` and `3 /
4`. -/
abbrev Overlap := LeftSet sq' ∩ RightSet sq'
/-- The open interval band between the two fixed cuts, used as the overlap parameter. -/
abbrev Parameter := Band lower upper

/-- The base overlap is the exact attaching-space product chart. -/
def overlapHomeomorph : A' × Parameter ≃ₜ (Overlap sq') :=
  (bandHomeomorph f' g' sq' lower upper).trans {
    toFun := fun z ↦ ⟨z.1, z.2.2, z.2.1⟩
    invFun := fun z ↦ ⟨z.1, z.2.2, z.2.1⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

/-- The original left square's strict comparison. -/
def leftEdge : C(A, {z : A' × B // b z.2 = f' z.1}) :=
  ⟨fun x ↦ ⟨(a x, f x), ConcreteCategory.congr_hom wf x⟩, by fun_prop⟩
/-- The original right square's strict comparison. -/
def rightEdge : C(A, {z : A' × C // c z.2 = g' z.1}) :=
  ⟨fun x ↦ ⟨(a x, g x), ConcreteCategory.congr_hom wg x⟩, by fun_prop⟩

/-- The strict pullback of `b` along the retraction of the target left collar to `B'`. -/
abbrev End0 := RetractionPullback.Space
  (leftCollarStrongDeformationRetract f' g' sq' upper zero_lt_upper) b
/-- The strict pullback of `c` along the retraction of the target right collar to `C'`. -/
abbrev End1 := RetractionPullback.Space
  (rightCollarStrongDeformationRetract f' g' sq' lower lower_lt_one) c

/-- Project the left collar pullback `End0` to its point in the target left collar. -/
def endProjection0 : TopCat.of (End0 sq' b) ⟶ TopCat.of (LeftSet sq') :=
  TopCat.ofHom (HomotopyPullback.strictBaseProjection b.hom
    (leftCollarProjection f' g' sq' upper zero_lt_upper).hom)
/-- Project the right collar pullback `End1` to its point in the target right collar. -/
def endProjection1 : TopCat.of (End1 sq' c) ⟶ TopCat.of (RightSet sq') :=
  TopCat.ofHom (HomotopyPullback.strictBaseProjection c.hom
    (rightCollarProjection f' g' sq' lower lower_lt_one).hom)

/-- Map `A × Parameter` into the overlap restriction of `End0` by the strict left edge comparison
and the left pullback band chart. -/
def overlapMap0 : TopCat.of (A × Parameter) ⟶
    TopCat.of {z : End0 sq' b // (endProjection0 sq' b z).1 ∈ RightSet sq'} :=
  TopCat.ofHom ⟨fun z ↦ leftPullbackBandHomeomorph f' g' sq' lower upper zero_lt_upper b
    (leftEdge a b wf z.1, z.2), by fun_prop⟩

/-- Map `A × Parameter` into the overlap restriction of `End1` by the strict right edge
comparison and the right pullback band chart. -/
def overlapMap1 : TopCat.of (A × Parameter) ⟶
    TopCat.of {z : End1 sq' c // (endProjection1 sq' c z).1 ∈ LeftSet sq'} :=
  TopCat.ofHom ⟨fun z ↦ rightPullbackBandHomeomorph f' g' sq' lower upper lower_lt_one c
    (rightEdge a c wg z.1, z.2), by fun_prop⟩

/-- A completely explicit span of genuine collar pullbacks for the map
of double cylinders. Its overlap is the actual attaching-space product. -/
def data : FibrationSpan.Data D' (LeftSet sq') (RightSet sq') where
  E0 := TopCat.of (End0 sq' b)
  E1 := TopCat.of (End1 sq' c)
  R := TopCat.of (A × Parameter)
  p0 := endProjection0 sq' b
  p1 := endProjection1 sq' c
  k0 := overlapMap0 sq' a b wf
  k1 := overlapMap1 sq' a c wg
  over _ := rfl

@[simp] theorem data_overlap_base (z : A × Parameter) :
    (data sq' a b c wf wg).q0 ((data sq' a b c wf wg).k0 z) =
      overlapHomeomorph sq' (a z.1, z.2) := rfl

/-- Both actual end projections are fibrations whenever the original
vertical endpoint maps are. -/
theorem endProjection0_lifting (hb : HomotopyLiftingProperty b.hom) :
    HomotopyLiftingProperty (endProjection0 sq' b).hom :=
  HomotopyLiftingProperty.baseChange _ _ hb
theorem endProjection1_lifting (hc : HomotopyLiftingProperty c.hom) :
    HomotopyLiftingProperty (endProjection1 sq' c).hom :=
  HomotopyLiftingProperty.baseChange _ _ hc

/-- The actual common overlap projection is the original fibration
cross the interval band, transported through the proved product chart. -/
theorem overlap_lifting (ha : HomotopyLiftingProperty a.hom) :
    HomotopyLiftingProperty ((data sq' a b c wf wg).k0 ≫ (data sq' a b c wf wg).q0).hom := by
  apply (ha.prod_id Parameter).of_targetHomeomorph _ (overlapHomeomorph sq').symm
  apply ContinuousMap.ext
  intro z
  change (overlapHomeomorph sq').symm ((data sq' a b c wf wg).q0
    ((data sq' a b c wf wg).k0 z)) = (a z.1, z.2)
  rw [data_overlap_base, Homeomorph.symm_apply_apply]

/-- Actual ordinary homotopy equivalence of the left edge comparison
gives the required overlap equivalence, retaining its canonical map. -/
def overlapEquiv0
    (E : ContinuousMap.HomotopyEquiv A {z : A' × B // b z.2 = f' z.1}) :
    ContinuousMap.HomotopyEquiv (A × Parameter) (data sq' a b c wf wg).Q0 :=
  (E.prodCongr (ContinuousMap.HomotopyEquiv.refl Parameter)).trans
    (leftPullbackBandHomeomorph f' g' sq' lower upper zero_lt_upper b).toHomotopyEquiv

theorem overlapEquiv0_toFun
    (E : ContinuousMap.HomotopyEquiv A {z : A' × B // b z.2 = f' z.1})
    (he : E.toFun = leftEdge a b wf) :
    (overlapEquiv0 sq' a b c wf wg E).toFun = (data sq' a b c wf wg).k0.hom := by
  apply ContinuousMap.ext
  intro z
  change leftPullbackBandHomeomorph f' g' sq' lower upper zero_lt_upper b (E.toFun z.1, z.2) = _
  rw [he]
  rfl

/-- Extend a homotopy equivalence from `A` to the strict right edge pullback across `Parameter`,
then transport it to the overlap restriction `Q1` through the right pullback band chart. -/
def overlapEquiv1
    (E : ContinuousMap.HomotopyEquiv A {z : A' × C // c z.2 = g' z.1}) :
    ContinuousMap.HomotopyEquiv (A × Parameter) (data sq' a b c wf wg).Q1 :=
  (E.prodCongr (ContinuousMap.HomotopyEquiv.refl Parameter)).trans
    (rightPullbackBandHomeomorph f' g' sq' lower upper lower_lt_one c).toHomotopyEquiv

theorem overlapEquiv1_toFun
    (E : ContinuousMap.HomotopyEquiv A {z : A' × C // c z.2 = g' z.1})
    (he : E.toFun = rightEdge a c wg) :
    (overlapEquiv1 sq' a b c wf wg E).toFun = (data sq' a b c wf wg).k1.hom := by
  apply ContinuousMap.ext
  intro z
  change rightPullbackBandHomeomorph f' g' sq' lower upper lower_lt_one c (E.toFun z.1, z.2) = _
  rw [he]
  rfl

/-- The instantiated finite normalization is globally weakly lifting.
Only genuine vertical fibrations and the two original strict cartesian
comparison equivalences are assumed. -/
theorem normalized_weakLifting
    (ha : HomotopyLiftingProperty a.hom) (hb : HomotopyLiftingProperty b.hom)
    (hc : HomotopyLiftingProperty c.hom)
    (E : ContinuousMap.HomotopyEquiv A {z : A' × B // b z.2 = f' z.1})
    (he : E.toFun = leftEdge a b wf)
    (F : ContinuousMap.HomotopyEquiv A {z : A' × C // c z.2 = g' z.1})
    (hf : F.toFun = rightEdge a c wg) :
    WeakHomotopyLiftingProperty (data sq' a b c wf wg).normalized.projection.hom := by
  apply (data sq' a b c wf wg).weakLifting (height f' g' sq')
    rfl (by
      ext x
      change (1 / 4 : ℝ) < (height f' g' sq' x : ℝ) ↔
        1 - (height f' g' sq' x : ℝ) < 3 / 4
      constructor <;> intro h <;> linarith)
    (endProjection0_lifting sq' b hb) (endProjection1_lifting sq' c hc)
    (overlap_lifting sq' a b c wf wg ha)
    (overlapEquiv0 sq' a b c wf wg E) (overlapEquiv0_toFun sq' a b c wf wg E he)
    (overlapEquiv1 sq' a b c wf wg F) (overlapEquiv1_toFun sq' a b c wf wg F hf)

end TopCat.DoubleCylinder.FiniteNormalization
