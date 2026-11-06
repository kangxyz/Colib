/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DoubleMappingCylinder.Basic
public import Colib.Topology.Pushout.Open.Restriction
public import Colib.Topology.DeformationRetract.FiberwisePushout

/-!
# Open collars in an actual double mapping cylinder

The two height collars are genuine open subspaces of the ordinary pushout.
Their strong deformation retractions are obtained by restricting that pushout
and contracting the remaining half-open interval, without a quotient
base-change assumption.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/Collars.lean` at commit
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

private def sumLeftHomeomorph {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (P : X ⊕ Y → Prop) (hl : ∀ x, P (Sum.inl x)) (hr : ∀ y, ¬ P (Sum.inr y)) :
    X ≃ₜ {z : X ⊕ Y // P z} := by
  let m : X → {z : X ⊕ Y // P z} := fun x ↦ ⟨Sum.inl x, hl x⟩
  have hm : IsEmbedding m := IsEmbedding.subtypeVal.of_comp_iff.mp IsEmbedding.inl
  apply hm.toHomeomorphOfSurjective
  rintro ⟨x | y, h⟩
  · exact ⟨x, rfl⟩
  · exact False.elim (hr y h)

private def sumRightHomeomorph {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (P : X ⊕ Y → Prop) (hl : ∀ x, ¬ P (Sum.inl x)) (hr : ∀ y, P (Sum.inr y)) :
    Y ≃ₜ {z : X ⊕ Y // P z} := by
  let m : Y → {z : X ⊕ Y // P z} := fun y ↦ ⟨Sum.inr y, hr y⟩
  have hm : IsEmbedding m := IsEmbedding.subtypeVal.of_comp_iff.mp IsEmbedding.inr
  apply hm.toHomeomorphOfSurjective
  rintro ⟨x | y, h⟩
  · exact False.elim (hl x h)
  · exact ⟨y, rfl⟩

variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e) (cut : I)

/-- The open collar containing the left endpoint. -/
def leftCollarSet : Set D := {d | height f g sq d < cut}
/-- The open collar containing the right endpoint. -/
def rightCollarSet : Set D := {d | cut < height f g sq d}

theorem leftCollar_isOpen : IsOpen (leftCollarSet f g sq cut) :=
  isOpen_lt (height f g sq).continuous continuous_const

theorem rightCollar_isOpen : IsOpen (rightCollarSet f g sq cut) :=
  isOpen_lt continuous_const (height f g sq).continuous

/-- Ordered left and right cutoffs give an open cover of the double cylinder. -/
theorem collar_cover (rightCut : I) (hcut : rightCut < cut) :
    leftCollarSet f g sq cut ∪ rightCollarSet f g sq rightCut = Set.univ := by
  ext d
  simp only [Set.mem_union, leftCollarSet, rightCollarSet, Set.mem_ofPred_eq,
    Set.mem_univ, iff_true]
  by_cases h : height f g sq d < cut
  · exact Or.inl h
  · exact Or.inr (lt_of_lt_of_le hcut (le_of_not_gt h))

/-- The overlap is exactly the corresponding open height band. -/
theorem collar_intersection (rightCut : I) :
    leftCollarSet f g sq cut ∩ rightCollarSet f g sq rightCut =
    {d | rightCut < height f g sq d ∧ height f g sq d < cut} := by
  ext d
  exact and_comm

/-- The open subspace of the double cylinder consisting of points with height below `cut`. -/
abbrev LeftCollar : TopCat.{u} := OpenPushout.vertex (leftCollarSet f g sq cut)
/-- The open subspace of the double cylinder consisting of points with height above `cut`. -/
abbrev RightCollar : TopCat.{u} := OpenPushout.vertex (rightCollarSet f g sq cut)

/-- The cylinder corner of the left open restriction. -/
abbrev LeftCollarCylinder : TopCat.{u} :=
  TopCat.of {z : A × ULift.{u} I // height f g sq (l z) < cut}
/-- The cylinder corner of the right open restriction. -/
abbrev RightCollarCylinder : TopCat.{u} :=
  TopCat.of {z : A × ULift.{u} I // cut < height f g sq (l z)}

/-- The zero endpoint in the restricted left cylinder. -/
def leftCollarEndpoint (hcut : 0 < cut) : A ⟶ LeftCollarCylinder f g sq cut := TopCat.ofHom
  ⟨fun a ↦ ⟨(a, ULift.up 0), by
    change height f g sq (l (a, ULift.up 0)) < cut; rw [height_cylinder]; exact hcut⟩, by fun_prop⟩
/-- The one endpoint in the restricted right cylinder. -/
def rightCollarEndpoint (hcut : cut < 1) : A ⟶ RightCollarCylinder f g sq cut := TopCat.ofHom
  ⟨fun a ↦ ⟨(a, ULift.up 1), by
    change cut < height f g sq (l (a, ULift.up 1)); rw [height_cylinder]; exact hcut⟩, by fun_prop⟩

/-- The actual left endpoint inclusion into its collar. -/
def leftCollarInclusion (hcut : 0 < cut) : B ⟶ LeftCollar f g sq cut := TopCat.ofHom
  ⟨fun b ↦ ⟨e (Sum.inl b), by
    change height f g sq (e (Sum.inl b)) < cut; rw [height_left]; exact hcut⟩, by fun_prop⟩
/-- The actual right endpoint inclusion into its collar. -/
def rightCollarInclusion (hcut : cut < 1) : C ⟶ RightCollar f g sq cut := TopCat.ofHom
  ⟨fun c ↦ ⟨e (Sum.inr c), by
    change cut < height f g sq (e (Sum.inr c)); rw [height_right]; exact hcut⟩, by fun_prop⟩

/-- The cylinder inclusion into the left collar. -/
abbrev leftCollarCylinderInclusion : LeftCollarCylinder f g sq cut ⟶ LeftCollar f g sq cut :=
  OpenPushout.leftInclusion (g := l) (leftCollarSet f g sq cut)
/-- The cylinder inclusion into the right collar. -/
abbrev rightCollarCylinderInclusion : RightCollarCylinder f g sq cut ⟶ RightCollar f g sq cut :=
  OpenPushout.leftInclusion (g := l) (rightCollarSet f g sq cut)

/-- Restricting the ordinary pushout to the left collar leaves only its left end. -/
theorem leftCollar_isPushout (hcut : 0 < cut) : IsPushout (leftCollarEndpoint f g sq cut hcut) f
    (leftCollarCylinderInclusion f g sq cut) (leftCollarInclusion f g sq cut hcut) := by
  let es : A ≃ₜ OpenPushout.source (i := TopCat.intervalEndpoints A) (g := l)
      (leftCollarSet f g sq cut) := sumLeftHomeomorph _
    (fun a ↦ by
      change height f g sq (l (a, ULift.up 0)) < cut; rw [height_cylinder]; exact hcut)
    (fun a ↦ by
      change ¬ height f g sq (l (a, ULift.up 1)) < cut;
        rw [height_cylinder]; exact not_lt_of_ge cut.2.2)
  let et : B ≃ₜ OpenPushout.right (j := e) (leftCollarSet f g sq cut) :=
    sumLeftHomeomorph _ (fun b ↦ by
      change height f g sq (e (Sum.inl b)) < cut; rw [height_left]; exact hcut)
      (fun c ↦ by
        change ¬ height f g sq (e (Sum.inr c)) < cut; rw [height_right]; exact not_lt_of_ge cut.2.2)
  exact (OpenPushout.isPushout sq _ (leftCollar_isOpen f g sq cut)).of_iso'
    (TopCat.isoOfHomeo es) (Iso.refl _) (TopCat.isoOfHomeo et) (Iso.refl _)
    (by ext a; rfl) (by ext a; rfl) (by simp) (by ext b; rfl)

/-- Restricting the ordinary pushout to the right collar leaves only its right end. -/
theorem rightCollar_isPushout (hcut : cut < 1) : IsPushout (rightCollarEndpoint f g sq cut hcut) g
    (rightCollarCylinderInclusion f g sq cut) (rightCollarInclusion f g sq cut hcut) := by
  let es : A ≃ₜ OpenPushout.source (i := TopCat.intervalEndpoints A) (g := l)
      (rightCollarSet f g sq cut) := sumRightHomeomorph _
    (fun a ↦ by
      change ¬ cut < height f g sq (l (a, ULift.up 0));
        rw [height_cylinder]; exact not_lt_of_ge cut.2.1)
    (fun a ↦ by
      change cut < height f g sq (l (a, ULift.up 1)); rw [height_cylinder]; exact hcut)
  let et : C ≃ₜ OpenPushout.right (j := e) (rightCollarSet f g sq cut) :=
    sumRightHomeomorph _ (fun b ↦ by
      change ¬ cut < height f g sq (e (Sum.inl b)); rw [height_left]; exact not_lt_of_ge cut.2.1)
      (fun c ↦ by
        change cut < height f g sq (e (Sum.inr c)); rw [height_right]; exact hcut)
  exact (OpenPushout.isPushout sq _ (rightCollar_isOpen f g sq cut)).of_iso'
    (TopCat.isoOfHomeo es) (Iso.refl _) (TopCat.isoOfHomeo et) (Iso.refl _)
    (by ext a; rfl) (by ext a; rfl) (by simp) (by ext c; rfl)

/-- The left half-open cylinder contracts to zero by `(a,t,s) ↦ (a,s*t)`. -/
def leftCollarCylinderStrongDeformationRetract (hcut : 0 < cut) :
    TopCat.CylinderStrongDeformationRetract (leftCollarEndpoint f g sq cut hcut) where
  r := TopCat.ofHom ⟨fun z ↦ z.1.1, by fun_prop⟩
  retract := rfl
  H := TopCat.ofHom ⟨fun p ↦ ⟨(p.1.1.1, ULift.up (p.2.down * p.1.1.2.down)), by
      have ht : p.1.1.2.down < cut := by
        have hp := p.1.2
        change height f g sq (l (p.1.1.1, p.1.1.2)) < cut at hp
        rw [height_cylinder] at hp
        exact hp
      change height f g sq (l (p.1.1.1, ULift.up (p.2.down * p.1.1.2.down))) < cut
      rw [height_cylinder]
      exact lt_of_le_of_lt unitInterval.mul_le_right ht⟩,
    by
      apply Continuous.subtype_mk
      apply Continuous.prodMk
      · exact continuous_fst.subtype_val.fst
      · apply Continuous.comp continuous_uliftUp
        apply Continuous.subtype_mk
        change Continuous (fun p : LeftCollarCylinder f g sq cut × ULift.{u} I ↦
          (p.2.down : ℝ) * (p.1.1.2.down : ℝ))
        fun_prop⟩
  H₀ := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    change (z.1.1, ULift.up ((0 : I) * z.1.2.down)) = (z.1.1, ULift.up 0)
    simp
  H₁ := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    change (z.1.1, ULift.up ((1 : I) * z.1.2.down)) = z.1
    simp only [one_mul]
  fixed := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    apply Subtype.ext
    change (a, ULift.up (t.down * (0 : I))) = (a, ULift.up 0)
    simp

/-- The right half-open cylinder contracts to one by
`(a,t,s) ↦ (a,1-s*(1-t))`. -/
def rightCollarCylinderStrongDeformationRetract (hcut : cut < 1) :
    TopCat.CylinderStrongDeformationRetract (rightCollarEndpoint f g sq cut hcut) where
  r := TopCat.ofHom ⟨fun z ↦ z.1.1, by fun_prop⟩
  retract := rfl
  H := TopCat.ofHom ⟨fun p ↦ ⟨(p.1.1.1, ULift.up (σ (p.2.down * σ p.1.1.2.down))), by
      have ht : cut < p.1.1.2.down := by
        have hp := p.1.2
        change cut < height f g sq (l (p.1.1.1, p.1.1.2)) at hp
        rw [height_cylinder] at hp
        exact hp
      have hh : p.2.down * σ p.1.1.2.down ≤ σ p.1.1.2.down := unitInterval.mul_le_right
      change cut < height f g sq (l (p.1.1.1, ULift.up (σ (p.2.down * σ p.1.1.2.down))))
      rw [height_cylinder]
      change (cut : ℝ) < 1 - ((p.2.down : ℝ) * (1 - (p.1.1.2.down : ℝ)))
      change (p.2.down : ℝ) * (1 - (p.1.1.2.down : ℝ)) ≤ 1 - (p.1.1.2.down : ℝ) at hh
      change (cut : ℝ) < (p.1.1.2.down : ℝ) at ht
      linarith⟩, by
      apply Continuous.subtype_mk
      apply Continuous.prodMk
      · exact continuous_fst.subtype_val.fst
      · apply Continuous.comp continuous_uliftUp
        apply Continuous.subtype_mk
        change Continuous (fun p : RightCollarCylinder f g sq cut × ULift.{u} I ↦
          1 - (p.2.down : ℝ) * (1 - (p.1.1.2.down : ℝ)))
        fun_prop⟩
  H₀ := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    change (z.1.1, ULift.up (σ ((0 : I) * σ z.1.2.down))) = (z.1.1, ULift.up 1)
    simp
  H₁ := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    change (z.1.1, ULift.up (σ ((1 : I) * σ z.1.2.down))) = z.1
    simp only [one_mul, symm_symm]
  fixed := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    apply Subtype.ext
    change (a, ULift.up (σ (t.down * σ (1 : I)))) = (a, ULift.up 1)
    simp

/-- The actual left collar strongly deformation retracts onto `B`. -/
def leftCollarStrongDeformationRetract (hcut : 0 < cut) :
    TopCat.CylinderStrongDeformationRetract (leftCollarInclusion f g sq cut hcut) :=
  (leftCollarCylinderStrongDeformationRetract f g sq cut hcut).pushout (leftCollar_isPushout f g
    sq cut hcut)

/-- The actual right collar strongly deformation retracts onto `C`. -/
def rightCollarStrongDeformationRetract (hcut : cut < 1) :
    TopCat.CylinderStrongDeformationRetract (rightCollarInclusion f g sq cut hcut) :=
  (rightCollarCylinderStrongDeformationRetract f g sq cut hcut).pushout (rightCollar_isPushout f
    g sq cut hcut)

/-- Explicit left collar collapse. -/
abbrev leftCollarProjection (hcut : 0 < cut) : LeftCollar f g sq cut ⟶ B :=
  (leftCollarStrongDeformationRetract f g sq cut hcut).r

/-- Explicit right collar collapse. -/
abbrev rightCollarProjection (hcut : cut < 1) : RightCollar f g sq cut ⟶ C :=
  (rightCollarStrongDeformationRetract f g sq cut hcut).r

@[simp] theorem leftCollarProjection_cylinder (hcut : 0 < cut)
    (z : LeftCollarCylinder f g sq cut) :
    leftCollarProjection f g sq cut hcut (leftCollarCylinderInclusion f g sq cut z) =
      f z.1.1 :=
  ConcreteCategory.congr_hom
    ((leftCollarCylinderStrongDeformationRetract f g sq cut hcut).pushout_inl_retraction
      (leftCollar_isPushout f g sq cut hcut)) z

@[simp] theorem rightCollarProjection_cylinder (hcut : cut < 1)
    (z : RightCollarCylinder f g sq cut) :
    rightCollarProjection f g sq cut hcut (rightCollarCylinderInclusion f g sq cut z) =
      g z.1.1 :=
  ConcreteCategory.congr_hom
    ((rightCollarCylinderStrongDeformationRetract f g sq cut hcut).pushout_inl_retraction
      (rightCollar_isPushout f g sq cut hcut)) z

@[simp] theorem leftCollarProjection_apply_cylinder (hcut : 0 < cut)
    (a : A) (t : TopCat.I) (ht : t.down < cut) :
    leftCollarProjection f g sq cut hcut
      ⟨l (a, t), by change height f g sq (l (a, t)) < cut; rwa [height_cylinder]⟩ = f a :=
  leftCollarProjection_cylinder f g sq cut hcut
    ⟨(a, t), by change height f g sq (l (a, t)) < cut; rwa [height_cylinder]⟩

@[simp] theorem rightCollarProjection_apply_cylinder (hcut : cut < 1)
    (a : A) (t : TopCat.I) (ht : cut < t.down) :
    rightCollarProjection f g sq cut hcut
      ⟨l (a, t), by change cut < height f g sq (l (a, t)); rwa [height_cylinder]⟩ = g a :=
  rightCollarProjection_cylinder f g sq cut hcut
    ⟨(a, t), by change cut < height f g sq (l (a, t)); rwa [height_cylinder]⟩

@[simp] theorem leftCollarProjection_end (hcut : 0 < cut) (b : B) :
    leftCollarProjection f g sq cut hcut (leftCollarInclusion f g sq cut hcut b) = b :=
  ConcreteCategory.congr_hom (leftCollarStrongDeformationRetract f g sq cut hcut).retract b

@[simp] theorem rightCollarProjection_end (hcut : cut < 1) (c : C) :
    rightCollarProjection f g sq cut hcut (rightCollarInclusion f g sq cut hcut c) = c :=
  ConcreteCategory.congr_hom (rightCollarStrongDeformationRetract f g sq cut hcut).retract c

/-- The glued left homotopy has the literal multiplication formula on the cylinder. -/
theorem leftCollarDeformation_cylinder (hcut : 0 < cut)
    (z : LeftCollarCylinder f g sq cut) (s : TopCat.I) :
    ((leftCollarStrongDeformationRetract f g sq cut hcut).H
      (leftCollarCylinderInclusion f g sq cut z, s)).1 =
      l (z.1.1, ULift.up (s.down * z.1.2.down)) :=
  congrArg Subtype.val (ConcreteCategory.congr_hom
    ((leftCollarCylinderStrongDeformationRetract f g sq cut hcut).pushout_inl_homotopy
      (leftCollar_isPushout f g sq cut hcut)) (z, s))

/-- The glued right homotopy has the literal reflected multiplication formula. -/
theorem rightCollarDeformation_cylinder (hcut : cut < 1)
    (z : RightCollarCylinder f g sq cut) (s : TopCat.I) :
    ((rightCollarStrongDeformationRetract f g sq cut hcut).H
      (rightCollarCylinderInclusion f g sq cut z, s)).1 =
      l (z.1.1, ULift.up (σ (s.down * σ z.1.2.down))) :=
  congrArg Subtype.val (ConcreteCategory.congr_hom
    ((rightCollarCylinderStrongDeformationRetract f g sq cut hcut).pushout_inl_homotopy
      (rightCollar_isPushout f g sq cut hcut)) (z, s))

@[simp] theorem leftCollarDeformation_end (hcut : 0 < cut) (b : B) (s : TopCat.I) :
    (leftCollarStrongDeformationRetract f g sq cut hcut).H
      (leftCollarInclusion f g sq cut hcut b, s) = leftCollarInclusion f g sq cut hcut b :=
  ConcreteCategory.congr_hom (leftCollarStrongDeformationRetract f g sq cut hcut).fixed (b, s)

@[simp] theorem rightCollarDeformation_end (hcut : cut < 1) (c : C) (s : TopCat.I) :
    (rightCollarStrongDeformationRetract f g sq cut hcut).H
      (rightCollarInclusion f g sq cut hcut c, s) = rightCollarInclusion f g sq cut hcut c :=
  ConcreteCategory.congr_hom (rightCollarStrongDeformationRetract f g sq cut hcut).fixed (c, s)

/-- A base projection defined only on the left collar is preserved whenever
its cylinder restriction is independent of height. -/
theorem leftCollarDeformation_over_collar {T : TopCat.{u}} (hcut : 0 < cut)
    (p : LeftCollar f g sq cut ⟶ T) (a : A ⟶ T)
    (hp : ∀ z : LeftCollarCylinder f g sq cut,
      p (leftCollarCylinderInclusion f g sq cut z) = a z.1.1) :
    (leftCollarStrongDeformationRetract f g sq cut hcut).H ≫ p =
      fst (LeftCollar f g sq cut) TopCat.I ≫ p := by
  apply (leftCollarCylinderStrongDeformationRetract f g sq cut hcut).pushout_homotopy_over
    (leftCollar_isPushout f g sq cut hcut)
  apply ConcreteCategory.hom_ext
  rintro ⟨z, s⟩
  exact (hp ((leftCollarCylinderStrongDeformationRetract f g sq cut hcut).H (z, s))).trans
    (hp z).symm

/-- A base projection defined only on the right collar is preserved whenever
its cylinder restriction is independent of height. -/
theorem rightCollarDeformation_over_collar {T : TopCat.{u}} (hcut : cut < 1)
    (p : RightCollar f g sq cut ⟶ T) (a : A ⟶ T)
    (hp : ∀ z : RightCollarCylinder f g sq cut,
      p (rightCollarCylinderInclusion f g sq cut z) = a z.1.1) :
    (rightCollarStrongDeformationRetract f g sq cut hcut).H ≫ p =
      fst (RightCollar f g sq cut) TopCat.I ≫ p := by
  apply (rightCollarCylinderStrongDeformationRetract f g sq cut hcut).pushout_homotopy_over
    (rightCollar_isPushout f g sq cut hcut)
  apply ConcreteCategory.hom_ext
  rintro ⟨z, s⟩
  exact (hp ((rightCollarCylinderStrongDeformationRetract f g sq cut hcut).H (z, s))).trans
    (hp z).symm

/-- The left collar's retraction is over any such locally defined base map. -/
theorem leftCollarProjection_over_collar {T : TopCat.{u}} (hcut : 0 < cut)
    (p : LeftCollar f g sq cut ⟶ T) (a : A ⟶ T)
    (hp : ∀ z : LeftCollarCylinder f g sq cut,
      p (leftCollarCylinderInclusion f g sq cut z) = a z.1.1) :
    leftCollarProjection f g sq cut hcut ≫ leftCollarInclusion f g sq cut hcut ≫ p = p := by
  have hh := congrArg (fun k ↦ TopCat.ι₀ ≫ k)
    (leftCollarDeformation_over_collar f g sq cut hcut p a hp)
  simpa only [← Category.assoc, (leftCollarStrongDeformationRetract f g sq cut hcut).H₀,
    TopCat.ι₀_fst, Category.id_comp] using hh

/-- The right collar's retraction is over any such locally defined base map. -/
theorem rightCollarProjection_over_collar {T : TopCat.{u}} (hcut : cut < 1)
    (p : RightCollar f g sq cut ⟶ T) (a : A ⟶ T)
    (hp : ∀ z : RightCollarCylinder f g sq cut,
      p (rightCollarCylinderInclusion f g sq cut z) = a z.1.1) :
    rightCollarProjection f g sq cut hcut ≫ rightCollarInclusion f g sq cut hcut ≫ p = p := by
  have hh := congrArg (fun k ↦ TopCat.ι₀ ≫ k)
    (rightCollarDeformation_over_collar f g sq cut hcut p a hp)
  simpa only [← Category.assoc, (rightCollarStrongDeformationRetract f g sq cut hcut).H₀,
    TopCat.ι₀_fst, Category.id_comp] using hh

variable {T : TopCat.{u}} (p : D ⟶ T)

/-- Restriction of an actual base map to the left collar. -/
def leftCollarBaseMap : LeftCollar f g sq cut ⟶ T :=
  TopCat.ofHom ⟨fun d ↦ p d.1, by fun_prop⟩

/-- Restriction of an actual base map to the right collar. -/
def rightCollarBaseMap : RightCollar f g sq cut ⟶ T :=
  TopCat.ofHom ⟨fun d ↦ p d.1, by fun_prop⟩

variable (a : A ⟶ T) (hp : l ≫ p = fst A TopCat.I ≫ a)
include hp

/-- Every base map independent of the cylinder coordinate is preserved by
all stages of the left collar deformation. -/
theorem leftCollarDeformation_over (hcut : 0 < cut) :
    (leftCollarStrongDeformationRetract f g sq cut hcut).H ≫
        leftCollarBaseMap f g sq cut p =
      fst (LeftCollar f g sq cut) TopCat.I ≫ leftCollarBaseMap f g sq cut p := by
  apply (leftCollarCylinderStrongDeformationRetract f g sq cut hcut).pushout_homotopy_over
    (leftCollar_isPushout f g sq cut hcut)
  apply ConcreteCategory.hom_ext
  rintro ⟨z, s⟩
  change p (l (z.1.1, ULift.up (s.down * z.1.2.down))) = p (l z.1)
  exact (ConcreteCategory.congr_hom hp (z.1.1, ULift.up (s.down * z.1.2.down))).trans
    (ConcreteCategory.congr_hom hp z.1).symm

/-- Every base map independent of the cylinder coordinate is preserved by
all stages of the right collar deformation. -/
theorem rightCollarDeformation_over (hcut : cut < 1) :
    (rightCollarStrongDeformationRetract f g sq cut hcut).H ≫
        rightCollarBaseMap f g sq cut p =
      fst (RightCollar f g sq cut) TopCat.I ≫ rightCollarBaseMap f g sq cut p := by
  apply (rightCollarCylinderStrongDeformationRetract f g sq cut hcut).pushout_homotopy_over
    (rightCollar_isPushout f g sq cut hcut)
  apply ConcreteCategory.hom_ext
  rintro ⟨z, s⟩
  change p (l (z.1.1, ULift.up (σ (s.down * σ z.1.2.down)))) = p (l z.1)
  exact (ConcreteCategory.congr_hom hp
    (z.1.1, ULift.up (σ (s.down * σ z.1.2.down)))).trans
    (ConcreteCategory.congr_hom hp z.1).symm

/-- The left collar collapse is strictly over every such base. -/
theorem leftCollarProjection_over (hcut : 0 < cut) :
    leftCollarProjection f g sq cut hcut ≫ leftCollarInclusion f g sq cut hcut ≫
        leftCollarBaseMap f g sq cut p = leftCollarBaseMap f g sq cut p := by
  have hh := congrArg (fun k ↦ TopCat.ι₀ ≫ k)
    (leftCollarDeformation_over f g sq cut p a hp hcut)
  simpa only [← Category.assoc, (leftCollarStrongDeformationRetract f g sq cut hcut).H₀,
    TopCat.ι₀_fst, Category.id_comp] using hh

/-- The right collar collapse is strictly over every such base. -/
theorem rightCollarProjection_over (hcut : cut < 1) :
    rightCollarProjection f g sq cut hcut ≫ rightCollarInclusion f g sq cut hcut ≫
        rightCollarBaseMap f g sq cut p = rightCollarBaseMap f g sq cut p := by
  have hh := congrArg (fun k ↦ TopCat.ι₀ ≫ k)
    (rightCollarDeformation_over f g sq cut p a hp hcut)
  simpa only [← Category.assoc, (rightCollarStrongDeformationRetract f g sq cut hcut).H₀,
    TopCat.ι₀_fst, Category.id_comp] using hh

end TopCat.DoubleCylinder
