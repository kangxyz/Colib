/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.Restriction
public import Colib.Topology.Pushout.HomotopyEquivalence
public import Colib.Topology.DoubleMappingCylinder.LocalComparison
public import Colib.Topology.DoubleMappingCylinder.Band
public import Colib.Topology.HomotopyPullback.Retraction
public import Colib.Topology.OpenCover.TwoSet.CylinderInvariance
public import Colib.Topology.DoubleMappingCylinder.HeightCover

/-!
# Double-cylinder comparison for homotopy pullbacks

The double-cylinder comparison map, its local restrictions and gluing give the stated homotopy
equivalence with the path-space homotopy pullback.
-/
/-! Implementation source: `Quillen/Topology/HomotopyPullback/DoubleCylinder.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual path-space comparisons and
pushout hypotheses are retained. -/
@[expose] public section

open Topology TopCat

open TopCat.DoubleCylinder


noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.DoubleCylinder.HomotopyPullback

variable {A B C D E T : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (TopCat.intervalEndpoints A) (DoubleCylinder.endMap f g) l e)
  (q : E ⟶ T) (b : B ⟶ T) (c : C ⟶ T) (w : f ≫ b = g ≫ c)

/-- The map from the disjoint union of the endpoint spaces to `T`, given by `b` on `B` and `c` on
`C`. -/
def parameterEnds : TopCat.of (B ⊕ C) ⟶ T :=
  TopCat.ofHom ⟨Sum.elim b c, continuous_sum_dom.mpr ⟨b.hom.continuous, c.hom.continuous⟩⟩

include w in
theorem parameter_square :
    TopCat.intervalEndpoints A ≫ (fst A TopCat.I ≫ f ≫ b) =
      DoubleCylinder.endMap f g ≫ parameterEnds b c := by
  apply ConcreteCategory.hom_ext
  intro x
  cases x with
  | inl a => rfl
  | inr a => exact ConcreteCategory.congr_hom w a

/-- The common parameter map, constant along each cylinder segment. -/
def parameter : D ⟶ T :=
  sq.desc (fst A TopCat.I ≫ f ≫ b) (parameterEnds b c) (parameter_square f g b c w)

@[simp] theorem parameter_cylinder (a : A) (t : TopCat.I) :
    parameter f g sq b c w (l (a, t)) = b (f a) :=
  ConcreteCategory.congr_hom (sq.inl_desc _ _ _) (a, t)

@[simp] theorem parameter_left (x : B) :
    parameter f g sq b c w (e (Sum.inl x)) = b x :=
  ConcreteCategory.congr_hom (sq.inr_desc _ _ _) (Sum.inl x)

@[simp] theorem parameter_right (x : C) :
    parameter f g sq b c w (e (Sum.inr x)) = c x :=
  ConcreteCategory.congr_hom (sq.inr_desc _ _ _) (Sum.inr x)

/-- The homotopy pullback of `q` and the common parameter map `f ≫ b` on the attaching space `A`. -/
abbrev HA : TopCat.{u} := TopCat.of (Topology.HomotopyPullback q.hom (b.hom.comp f.hom))
/-- The homotopy pullback of `q` and the left endpoint parameter map `b`. -/
abbrev HB : TopCat.{u} := TopCat.of (Topology.HomotopyPullback q.hom b.hom)
/-- The homotopy pullback of `q` and the right endpoint parameter map `c`. -/
abbrev HC : TopCat.{u} := TopCat.of (Topology.HomotopyPullback q.hom c.hom)

/-- The left leg leaves the source and path coordinates unchanged. -/
def leftLeg : HA f q b ⟶ HB q b :=
  TopCat.ofHom ⟨fun z ↦ ⟨(f z.1.1, z.1.2), z.2⟩, by fun_prop⟩

/-- The right leg leaves the source and path coordinates unchanged. -/
def rightLeg : HA f q b ⟶ HC q c :=
  TopCat.ofHom ⟨fun z ↦ ⟨(g z.1.1, z.1.2), z.2.1,
    z.2.2.trans (ConcreteCategory.congr_hom w z.1.1)⟩, by fun_prop⟩

@[simp] theorem leftLeg_val (z : HA f q b) : (leftLeg f q b z).1 =
    (f z.1.1, z.1.2) := rfl

@[simp] theorem rightLeg_val (z : HA f q b) : (rightLeg f g q b c w z).1 =
    (g z.1.1, z.1.2) := rfl

/-- The homotopy pullback of `q` and the parameter map on the total double cylinder. -/
abbrev Target : TopCat.{u} :=
  TopCat.of (Topology.HomotopyPullback q.hom (parameter f g sq b c w).hom)

/-- Map the cylinder on `HA` into `Target` by applying its cylinder inclusion to the `A` and
interval coordinates and retaining the `q`-source and path coordinates. -/
def cylinderComparison : HA f q b ⊗ TopCat.I ⟶ Target f g sq q b c w :=
  TopCat.ofHom ⟨fun z ↦ ⟨(l (z.1.1.1, z.2), z.1.1.2), z.1.2.1,
    z.1.2.2.trans (parameter_cylinder f g sq b c w z.1.1.1 z.2).symm⟩, by fun_prop⟩

/-- Map the left endpoint homotopy pullback `HB` into `Target` using the inclusion of `B` into
the double cylinder and retaining the source and path coordinates. -/
def leftComparison : HB q b ⟶ Target f g sq q b c w :=
  TopCat.ofHom ⟨fun z ↦ ⟨(e (Sum.inl z.1.1), z.1.2), z.2.1,
    z.2.2.trans (parameter_left f g sq b c w z.1.1).symm⟩, by fun_prop⟩

/-- Map the right endpoint homotopy pullback `HC` into `Target` using the inclusion of `C` into
the double cylinder and retaining the source and path coordinates. -/
def rightComparison : HC q c ⟶ Target f g sq q b c w :=
  TopCat.ofHom ⟨fun z ↦ ⟨(e (Sum.inr z.1.1), z.1.2), z.2.1,
    z.2.2.trans (parameter_right f g sq b c w z.1.1).symm⟩, by fun_prop⟩

/-- Combine the left and right endpoint comparisons into a map from `HB ⊕ HC` to the homotopy
pullback over the total double cylinder. -/
def endsComparison : TopCat.of (HB q b ⊕ HC q c) ⟶ Target f g sq q b c w :=
  TopCat.ofHom ⟨Sum.elim (leftComparison f g sq q b c w) (rightComparison f g sq q b c w),
    continuous_sum_dom.mpr ⟨(leftComparison f g sq q b c w).hom.continuous,
      (rightComparison f g sq q b c w).hom.continuous⟩⟩

theorem comparison_square :
    TopCat.intervalEndpoints (HA f q b) ≫ cylinderComparison f g sq q b c w =
      DoubleCylinder.endMap (leftLeg f q b) (rightLeg f g q b c w) ≫
        endsComparison f g sq q b c w := by
  apply ConcreteCategory.hom_ext
  intro z
  cases z with
  | inl z =>
    apply Subtype.ext
    apply Prod.ext
    · exact ConcreteCategory.congr_hom sq.w (Sum.inl z.1.1)
    · rfl
  | inr z =>
    apply Subtype.ext
    apply Prod.ext
    · exact ConcreteCategory.congr_hom sq.w (Sum.inr z.1.1)
    · rfl

variable {Z : TopCat.{u}} {lh : HA f q b ⊗ TopCat.I ⟶ Z}
  {eh : TopCat.of (HB q b ⊕ HC q c) ⟶ Z}
  (sqH : IsPushout (TopCat.intervalEndpoints (HA f q b))
    (DoubleCylinder.endMap (leftLeg f q b) (rightLeg f g q b c w)) lh eh)

/-- The canonical comparison to the homotopy pullback over the total base. -/
def comparison : Z ⟶ Target f g sq q b c w :=
  sqH.desc (cylinderComparison f g sq q b c w) (endsComparison f g sq q b c w)
    (comparison_square f g sq q b c w)

@[simp] theorem comparison_cylinder (z : HA f q b) (t : TopCat.I) :
    (comparison f g sq q b c w sqH (lh (z, t))).1 = (l (z.1.1, t), z.1.2) :=
  congrArg Subtype.val (ConcreteCategory.congr_hom (sqH.inl_desc (cylinderComparison f g sq q b c w)
    (endsComparison f g sq q b c w) (comparison_square f g sq q b c w)) (z, t))

@[simp] theorem comparison_left (z : HB q b) :
    (comparison f g sq q b c w sqH (eh (Sum.inl z))).1 = (e (Sum.inl z.1.1), z.1.2) :=
  congrArg Subtype.val (ConcreteCategory.congr_hom (sqH.inr_desc (cylinderComparison f g sq q b c w)
    (endsComparison f g sq q b c w) (comparison_square f g sq q b c w)) (Sum.inl z))

@[simp] theorem comparison_right (z : HC q c) :
    (comparison f g sq q b c w sqH (eh (Sum.inr z))).1 = (e (Sum.inr z.1.1), z.1.2) :=
  congrArg Subtype.val (ConcreteCategory.congr_hom (sqH.inr_desc (cylinderComparison f g sq q b c w)
    (endsComparison f g sq q b c w) (comparison_square f g sq q b c w)) (Sum.inr z))

/-- The comparison lies over the canonical map of double cylinders. -/
theorem comparison_base :
    comparison f g sq q b c w sqH ≫
        TopCat.ofHom (Topology.HomotopyPullback.baseProjection q.hom (parameter f g sq b c w).hom) =
      DoubleCylinder.map sqH sq
        (TopCat.ofHom (Topology.HomotopyPullback.baseProjection q.hom (f ≫ b).hom))
        (TopCat.ofHom (Topology.HomotopyPullback.baseProjection q.hom b.hom))
        (TopCat.ofHom (Topology.HomotopyPullback.baseProjection q.hom c.hom)) rfl rfl := by
  apply ConcreteCategory.hom_ext
  intro x
  rcases Types.eq_or_eq_of_isPushout (sqH.map (forget TopCat)) x with
    ⟨⟨z, t⟩, h⟩ | ⟨z | z, h⟩
  · change lh (z, t) = x at h
    subst x
    change (comparison f g sq q b c w sqH (lh (z, t))).1.1 = _
    rw [DoubleCylinder.map_cylinder_apply]
    exact congrArg Prod.fst (comparison_cylinder f g sq q b c w sqH z t)
  · change eh (Sum.inl z) = x at h
    subst x
    change (comparison f g sq q b c w sqH (eh (Sum.inl z))).1.1 = _
    rw [DoubleCylinder.map_left]
    exact congrArg Prod.fst (comparison_left f g sq q b c w sqH z)
  · change eh (Sum.inr z) = x at h
    subst x
    change (comparison f g sq q b c w sqH (eh (Sum.inr z))).1.1 = _
    rw [DoubleCylinder.map_right]
    exact congrArg Prod.fst (comparison_right f g sq q b c w sqH z)

@[simp] theorem height_comparison (x : Z) :
    DoubleCylinder.height f g sq (comparison f g sq q b c w sqH x).1.1 =
      DoubleCylinder.height (leftLeg f q b) (rightLeg f g q b c w) sqH x := by
  have h := ConcreteCategory.congr_hom (comparison_base f g sq q b c w sqH) x
  change (comparison f g sq q b c w sqH x).1.1 = _ at h
  rw [h, DoubleCylinder.height_map]

variable (lo hi : I)

/-- The homotopy-pullback target restricted to the same open height band. -/
abbrev TargetBand :=
  {z : Target f g sq q b c w //
    lo < DoubleCylinder.height f g sq z.1.1 ∧ DoubleCylinder.height f g sq z.1.1 < hi}

/-- The exact product chart for the target's middle band. -/
def targetBandHomeomorph : HA f q b × DoubleCylinder.Band lo hi ≃ₜ
    TargetBand f g sq q b c w lo hi := by
  let S : Set D := {d | lo < DoubleCylinder.height f g sq d ∧
    DoubleCylinder.height f g sq d < hi}
  let h := Topology.HomotopyPullback.parameterProductHomeomorph q.hom
    (Topology.HomotopyPullback.restrictedParameter (parameter f g sq b c w).hom S)
    (f ≫ b).hom (DoubleCylinder.bandHomeomorph f g sq lo hi)
    (fun a t ↦ parameter_cylinder f g sq b c w a (ULift.up t.1))
  exact h.trans (Topology.HomotopyPullback.restrictionHomeomorph q.hom
    (parameter f g sq b c w).hom S).symm

@[simp] theorem targetBandHomeomorph_val (z : HA f q b × DoubleCylinder.Band lo hi) :
    (targetBandHomeomorph f g sq q b c w lo hi z).1.1 =
      (l (z.1.1.1, ULift.up z.2.1), z.1.1.2) := rfl

/-- The canonical comparison restricted to the open middle band. -/
def bandComparison :
    C(DoubleCylinder.BandSpace (leftLeg f q b) (rightLeg f g q b c w) sqH lo hi,
      TargetBand f g sq q b c w lo hi) :=
  ⟨fun z ↦ ⟨comparison f g sq q b c w sqH z.1, by
    simpa only [height_comparison f g sq q b c w sqH] using z.2⟩, by fun_prop⟩

/-- The middle-band restriction is an actual homeomorphism, because both
sides have the identical homotopy-pullback-times-band coordinates. -/
def bandComparisonHomeomorph :
    DoubleCylinder.BandSpace (leftLeg f q b) (rightLeg f g q b c w) sqH lo hi ≃ₜ
      TargetBand f g sq q b c w lo hi :=
  (DoubleCylinder.bandHomeomorph (leftLeg f q b) (rightLeg f g q b c w) sqH lo hi).symm.trans
    (targetBandHomeomorph f g sq q b c w lo hi)

@[simp] theorem bandComparisonHomeomorph_apply
    (z : DoubleCylinder.BandSpace (leftLeg f q b) (rightLeg f g q b c w) sqH lo hi) :
    bandComparisonHomeomorph f g sq q b c w sqH lo hi z =
      bandComparison f g sq q b c w sqH lo hi z := by
  obtain ⟨x, rfl⟩ :=
    (DoubleCylinder.bandHomeomorph (leftLeg f q b) (rightLeg f g q b c w) sqH lo hi).surjective z
  apply Subtype.ext
  apply Subtype.ext
  change (targetBandHomeomorph f g sq q b c w lo hi
    ((DoubleCylinder.bandHomeomorph (leftLeg f q b) (rightLeg f g q b c w)
      sqH lo hi).symm
      (DoubleCylinder.bandHomeomorph (leftLeg f q b) (rightLeg f g q b c w)
        sqH lo hi x))).1.1 = _
  rw [Homeomorph.symm_apply_apply, targetBandHomeomorph_val]
  exact (comparison_cylinder f g sq q b c w sqH x.1 (ULift.up x.2.1)).symm

/-- The homotopy equivalence between the middle-band restrictions induced by
`bandComparisonHomeomorph`, with the canonical comparison as its forward map. -/
def bandComparisonHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (DoubleCylinder.BandSpace (leftLeg f q b) (rightLeg f g q b c w) sqH lo hi)
      (TargetBand f g sq q b c w lo hi) :=
  (bandComparisonHomeomorph f g sq q b c w sqH lo hi).toHomotopyEquiv

@[simp] theorem bandComparisonHomotopyEquiv_toFun :
    (bandComparisonHomotopyEquiv f g sq q b c w sqH lo hi).toFun =
      bandComparison f g sq q b c w sqH lo hi := by
  apply ContinuousMap.ext
  intro z
  exact bandComparisonHomeomorph_apply f g sq q b c w sqH lo hi z

end TopCat.DoubleCylinder.HomotopyPullback

end

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.DoubleCylinder.HomotopyPullback
open DoubleCylinder

variable {A B C D E T : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (TopCat.intervalEndpoints A) (DoubleCylinder.endMap f g) l e)
  (q : E ⟶ T) (b : B ⟶ T) (c : C ⟶ T) (w : f ≫ b = g ≫ c)
  {Z : TopCat.{u}} {lh : HA f q b ⊗ TopCat.I ⟶ Z}
  {eh : TopCat.of (HB q b ⊕ HC q c) ⟶ Z}
  (sqH : IsPushout (TopCat.intervalEndpoints (HA f q b))
    (DoubleCylinder.endMap (leftLeg f q b) (rightLeg f g q b c w)) lh eh)
  (cut : I)

/-- The fixed parameter on a left collar factors exactly through its retraction. -/
theorem left_parameter_factor (hcut : 0 < cut) :
    Topology.HomotopyPullback.restrictedParameter (parameter f g sq b c w).hom
        (leftCollarSet f g sq cut) =
      b.hom.comp (leftCollarProjection f g sq cut hcut).hom := by
  ext x
  rcases Types.eq_or_eq_of_isPushout
    ((leftCollar_isPushout f g sq cut hcut).map (forget TopCat)) x with ⟨z, hz⟩ | ⟨y, hy⟩
  · change leftCollarCylinderInclusion f g sq cut z = x at hz
    subst x
    change parameter f g sq b c w (l z.1) =
      b (leftCollarProjection f g sq cut hcut (leftCollarCylinderInclusion f g sq cut z))
    rw [leftCollarProjection_cylinder]
    exact parameter_cylinder f g sq b c w z.1.1 z.1.2
  · change leftCollarInclusion f g sq cut hcut y = x at hy
    subst x
    change parameter f g sq b c w (e (Sum.inl y)) =
      b (leftCollarProjection f g sq cut hcut (leftCollarInclusion f g sq cut hcut y))
    rw [leftCollarProjection_end, parameter_left]

/-- The fixed parameter on a right collar factors exactly through its retraction. -/
theorem right_parameter_factor (hcut : cut < 1) :
    Topology.HomotopyPullback.restrictedParameter (parameter f g sq b c w).hom
        (rightCollarSet f g sq cut) =
      c.hom.comp (rightCollarProjection f g sq cut hcut).hom := by
  ext x
  rcases Types.eq_or_eq_of_isPushout
    ((rightCollar_isPushout f g sq cut hcut).map (forget TopCat)) x with ⟨z, hz⟩ | ⟨y, hy⟩
  · change rightCollarCylinderInclusion f g sq cut z = x at hz
    subst x
    change parameter f g sq b c w (l z.1) =
      c (rightCollarProjection f g sq cut hcut (rightCollarCylinderInclusion f g sq cut z))
    rw [rightCollarProjection_cylinder]
    exact (parameter_cylinder f g sq b c w z.1.1 z.1.2).trans
      (ConcreteCategory.congr_hom w z.1.1)
  · change rightCollarInclusion f g sq cut hcut y = x at hy
    subst x
    change parameter f g sq b c w (e (Sum.inr y)) =
      c (rightCollarProjection f g sq cut hcut (rightCollarInclusion f g sq cut hcut y))
    rw [rightCollarProjection_end, parameter_right]

/-- The subspace of `Target` whose double-cylinder coordinate lies in the left height collar
determined by `cut`. -/
abbrev LeftTarget :=
  {z : Target f g sq q b c w // z.1.1 ∈ leftCollarSet f g sq cut}
/-- The subspace of `Target` whose double-cylinder coordinate lies in the right height collar
determined by `cut`. -/
abbrev RightTarget :=
  {z : Target f g sq q b c w // z.1.1 ∈ rightCollarSet f g sq cut}

/-- The actual canonical comparison restricted to the left height collar. -/
def leftRestriction :
    C(LeftCollar (leftLeg f q b) (rightLeg f g q b c w) sqH cut,
      LeftTarget f g sq q b c w cut) :=
  ⟨fun x ↦ ⟨comparison f g sq q b c w sqH x.1, by
    change height f g sq (comparison f g sq q b c w sqH x.1).1.1 < cut
    rw [height_comparison]
    exact x.2⟩, by fun_prop⟩

/-- The actual canonical comparison restricted to the right height collar. -/
def rightRestriction :
    C(RightCollar (leftLeg f q b) (rightLeg f g q b c w) sqH cut,
      RightTarget f g sq q b c w cut) :=
  ⟨fun x ↦ ⟨comparison f g sq q b c w sqH x.1, by
    change cut < height f g sq (comparison f g sq q b c w sqH x.1).1.1
    rw [height_comparison]
    exact x.2⟩, by fun_prop⟩

/-- The canonical left collar restriction is an actual homotopy equivalence. -/
def leftRestrictionHomotopyEquiv (hcut : 0 < cut) :
    ContinuousMap.HomotopyEquiv
      (LeftCollar (leftLeg f q b) (rightLeg f g q b c w) sqH cut)
      (LeftTarget f g sq q b c w cut) := by
  let S := leftCollarStrongDeformationRetract
    (leftLeg f q b) (rightLeg f g q b c w) sqH cut hcut
  let R := leftCollarStrongDeformationRetract f g sq cut hcut
  let eT := Topology.HomotopyPullback.restrictionRetractionHomotopyEquiv
    q (parameter f g sq b c w) (leftCollarSet f g sq cut) R
    (leftCollarDeformation_projection sq cut hcut) b
    (left_parameter_factor f g sq b c w cut hcut)
  apply TopCat.homotopyEquivCancelLeft
    (a := TopCat.ofHom S.toHomotopyEquiv.toFun)
    (b := TopCat.ofHom (leftRestriction f g sq q b c w sqH cut))
    S.toHomotopyEquiv rfl eT
  have h : (leftRestriction f g sq q b c w sqH cut).comp S.toHomotopyEquiv.toFun =
      eT.toFun := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    exact comparison_left f g sq q b c w sqH z
  exact h.symm

/-- The canonical right collar restriction is an actual homotopy equivalence. -/
def rightRestrictionHomotopyEquiv (hcut : cut < 1) :
    ContinuousMap.HomotopyEquiv
      (RightCollar (leftLeg f q b) (rightLeg f g q b c w) sqH cut)
      (RightTarget f g sq q b c w cut) := by
  let S := rightCollarStrongDeformationRetract
    (leftLeg f q b) (rightLeg f g q b c w) sqH cut hcut
  let R := rightCollarStrongDeformationRetract f g sq cut hcut
  let eT := Topology.HomotopyPullback.restrictionRetractionHomotopyEquiv
    q (parameter f g sq b c w) (rightCollarSet f g sq cut) R
    (rightCollarDeformation_projection sq cut hcut) c
    (right_parameter_factor f g sq b c w cut hcut)
  apply TopCat.homotopyEquivCancelLeft
    (a := TopCat.ofHom S.toHomotopyEquiv.toFun)
    (b := TopCat.ofHom (rightRestriction f g sq q b c w sqH cut))
    S.toHomotopyEquiv rfl eT
  have h : (rightRestriction f g sq q b c w sqH cut).comp S.toHomotopyEquiv.toFun =
      eT.toFun := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    exact comparison_right f g sq q b c w sqH z
  exact h.symm

@[simp] theorem leftRestrictionHomotopyEquiv_toFun (hcut : 0 < cut) :
    (leftRestrictionHomotopyEquiv f g sq q b c w sqH cut hcut).toFun =
      leftRestriction f g sq q b c w sqH cut := rfl

@[simp] theorem rightRestrictionHomotopyEquiv_toFun (hcut : cut < 1) :
    (rightRestrictionHomotopyEquiv f g sq q b c w sqH cut hcut).toFun =
      rightRestriction f g sq q b c w sqH cut := rfl

/-- Fixed-target homotopy pullback commutes with a double mapping cylinder.
The proof uses the genuine collar retractions and the exact middle-band
homeomorphism, then glues the canonical restrictions over a two-open cover. -/
def comparisonHomotopyEquiv :
    ContinuousMap.HomotopyEquiv Z (Target f g sq q b c w) := by
  let hi : I := ⟨3 / 4, by constructor <;> norm_num⟩
  let lo : I := ⟨1 / 4, by constructor <;> norm_num⟩
  let k := (comparison f g sq q b c w sqH).hom
  let P := TwoOpenPartition.ofHeight ((height f g sq).comp
    (Topology.HomotopyPullback.baseProjection q.hom (parameter f g sq b c w).hom))
  let sL : (P.pullback k).Left ≃ₜ
      LeftCollar (leftLeg f q b) (rightLeg f g q b c w) sqH hi :=
    Homeomorph.setCongr (by
      ext x
      change (height f g sq (comparison f g sq q b c w sqH x).1.1 : ℝ) < 3 / 4 ↔ _
      rw [height_comparison]
      rfl)
  let sR : (P.pullback k).Right ≃ₜ
      RightCollar (leftLeg f q b) (rightLeg f g q b c w) sqH lo :=
    Homeomorph.setCongr (by
      ext x
      change 1 / 4 < (height f g sq (comparison f g sq q b c w sqH x).1.1 : ℝ) ↔ _
      rw [height_comparison]
      rfl)
  let sO : (P.pullback k).Overlap ≃ₜ
      BandSpace (leftLeg f q b) (rightLeg f g q b c w) sqH lo hi :=
    Homeomorph.setCongr (by
      ext x
      change ((height f g sq (comparison f g sq q b c w sqH x).1.1 : ℝ) < 3 / 4 ∧
        1 / 4 < (height f g sq (comparison f g sq q b c w sqH x).1.1 : ℝ)) ↔ _
      rw [height_comparison]
      exact and_comm)
  let tO : TargetBand f g sq q b c w lo hi ≃ₜ P.Overlap :=
    Homeomorph.setCongr (by
      ext x
      exact and_comm)
  let eL : ContinuousMap.HomotopyEquiv (P.pullback k).Left P.Left :=
    sL.toHomotopyEquiv.trans
      (leftRestrictionHomotopyEquiv f g sq q b c w sqH hi (by change (0 : ℝ) < 3 / 4; norm_num))
  let eR : ContinuousMap.HomotopyEquiv (P.pullback k).Right P.Right :=
    sR.toHomotopyEquiv.trans
      (rightRestrictionHomotopyEquiv f g sq q b c w sqH lo (by change (1 : ℝ) / 4 < 1; norm_num))
  let eO : ContinuousMap.HomotopyEquiv (P.pullback k).Overlap P.Overlap :=
    sO.toHomotopyEquiv.trans
      ((bandComparisonHomotopyEquiv f g sq q b c w sqH lo hi).trans tO.toHomotopyEquiv)
  apply P.homotopyEquivOfRestrictions k eL (by rfl) eR (by rfl) eO
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change ((bandComparisonHomotopyEquiv f g sq q b c w sqH lo hi).toFun (sO x)).1 = k x.1
  rw [bandComparisonHomotopyEquiv_toFun]
  rfl

@[simp] theorem comparisonHomotopyEquiv_toFun :
    (comparisonHomotopyEquiv f g sq q b c w sqH).toFun =
      (comparison f g sq q b c w sqH).hom := rfl

end TopCat.DoubleCylinder.HomotopyPullback

end
