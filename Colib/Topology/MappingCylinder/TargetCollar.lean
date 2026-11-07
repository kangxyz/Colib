/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.MappingCylinder.Fiberwise.HomotopyEquivalence
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-! # The actual target collar of a displayed mapping cylinder

Its height and target deformation use the original pushout legs. Restricting
the genuine target deformation gives a fiberwise SDR of every positive-height
collar, without an equivalence assumption on the attaching map.


Implementation provenance:
`Quillen/Topology/MappingCylinder/TargetCollar.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.MappingCylinder.TargetCollar
variable {A B M T : TopCat.{u}} {f : A ⟶ B}
  {l : A ⊗ TopCat.I ⟶ M} {c : B ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)

/-- The height map of the displayed mapping cylinder, equal to the interval coordinate on its
cylinder leg and to one on its target leg. -/
def heightMap : M ⟶ TopCat.I := sq.desc (snd A TopCat.I)
  (TopCat.ofHom (ContinuousMap.const B (ULift.up (1 : I)))) (by ext a; rfl)

@[reassoc (attr := simp)] theorem heightMap_cylinder : l ≫ heightMap sq = snd A TopCat.I :=
  sq.inl_desc _ _ _
@[reassoc (attr := simp)] theorem heightMap_target :
    c ≫ heightMap sq = TopCat.ofHom (ContinuousMap.const B (ULift.up (1 : I))) :=
  sq.inr_desc _ _ _

/-- The continuous mapping-cylinder height with values in the unlifted unit interval. -/
def height : C(M, I) := ⟨fun x ↦ (heightMap sq x).down, by fun_prop⟩

@[simp] theorem height_cylinder (z : A × ULift.{u} I) : height sq (l z) = z.2.down :=
  congrArg ULift.down (ConcreteCategory.congr_hom (heightMap_cylinder sq) z)
@[simp] theorem height_target (b : B) : height sq (c b) = 1 :=
  congrArg ULift.down (ConcreteCategory.congr_hom (heightMap_target sq) b)
theorem height_start (a : A) : height sq ((TopCat.ι₀ ≫ l) a) = 0 :=
  height_cylinder sq (a, ULift.up 0)

/-- Exact height of the original target deformation. -/
theorem height_deformation (x : M) (t : ULift.{u} I) :
    height sq ((TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract sq).H (x, t))
      =
      TopCat.MappingCylinder.intervalSlide (σ t.down) (height sq x) := by
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) x with ⟨z, rfl⟩ | ⟨b, rfl⟩
  · have h := ConcreteCategory.congr_hom
      (TopCat.MappingCylinder.pushoutDeformation_inl sq
        (TopCat.MappingCylinder.cylinderEndpointStrongDeformationRetract A)) (z, t)
    change (TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract sq).H (l z, t) =
      l (z.1, ULift.up (TopCat.MappingCylinder.intervalSlide (σ t.down) z.2.down)) at h
    change height sq ((TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract sq).H
      (l z, t)) =
      TopCat.MappingCylinder.intervalSlide (σ t.down) (height sq (l z))
    rw [h, height_cylinder, height_cylinder]
  · have h := ConcreteCategory.congr_hom
      (TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract sq).fixed (b, t)
    change (TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract sq).H (c b, t) = c
      b at h
    change height sq ((TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract sq).H
      (c b, t)) =
      TopCat.MappingCylinder.intervalSlide (σ t.down) (height sq (c b))
    rw [h, height_target, TopCat.MappingCylinder.intervalSlide_right]

theorem height_le_deformation (x : M) (t : ULift.{u} I) :
    height sq x ≤ height sq ((TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract
      sq).H
      (x, t)) := by
  rw [height_deformation]
  have h : σ (σ t.down) * σ (height sq x) ≤ σ (height sq x) := unitInterval.mul_le_right
  change (height sq x : ℝ) ≤ 1 - ((1 - ((σ t.down : I) : ℝ)) * (1 - (height sq x : ℝ)))
  change (1 - ((σ t.down : I) : ℝ)) * (1 - (height sq x : ℝ)) ≤ 1 - (height sq x : ℝ) at h
  linarith

variable (cut : I)
/-- The region of the mapping cylinder whose height is strictly greater than `cut`. -/
def collarSet : Set M := {x | cut < height sq x}
theorem collar_isOpen : IsOpen (collarSet sq cut) := isOpen_lt continuous_const (height
    sq).continuous
/-- The target height collar with its subspace topology. -/
abbrev Collar : TopCat.{u} := TopCat.of (collarSet sq cut)
/-- Include the target height collar into the displayed mapping cylinder. -/
def inclusion : Collar sq cut ⟶ M := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Restrict the original target inclusion to the height collar; `cut < 1` ensures that all
target points lie in this collar. -/
def target (hcut : cut < 1) : B ⟶ Collar sq cut := TopCat.ofHom
  ⟨fun b ↦ ⟨c b, by change cut < height sq (c b); simpa using hcut⟩, by fun_prop⟩
@[simp] theorem target_val (hcut : cut < 1) (b : B) : (target sq cut hcut b).val = c b := rfl
@[reassoc (attr := simp)] theorem target_inclusion (hcut : cut < 1) :
    target sq cut hcut ≫ inclusion sq cut = c := rfl

/-- Restriction of the unchanged mapping-cylinder target SDR. -/
def strongDeformationRetract (hcut : cut < 1) :
    TopCat.CylinderStrongDeformationRetract (target sq cut hcut) where
  r := inclusion sq cut ≫ TopCat.MappingCylinder.mappingCylinderProjection sq
  retract := by rw [← Category.assoc, target_inclusion,
    TopCat.MappingCylinder.mappingCylinderProjection_target]
  H := TopCat.ofHom ⟨fun z ↦
    ⟨(TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract sq).H (z.1.val, z.2),
      lt_of_lt_of_le z.1.property (height_le_deformation sq z.1.val z.2)⟩, by fun_prop⟩
  H₀ := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      (TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract
      sq).H₀ z.val
  H₁ := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      (TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract
      sq).H₁ z.val
  fixed := by
    apply ConcreteCategory.hom_ext
    rintro ⟨b, t⟩
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      (TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract
      sq).fixed (b, t)

@[simp] theorem retraction_apply (hcut : cut < 1) (z : Collar sq cut) :
    (strongDeformationRetract sq cut hcut).r z = TopCat.MappingCylinder.mappingCylinderProjection
      sq z.val := rfl
@[simp] theorem deformation_val (hcut : cut < 1) (z : Collar sq cut) (t : ULift.{u} I) :
    ((strongDeformationRetract sq cut hcut).H (z, t)).val =
      (TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract sq).H (z.val, t) := rfl

/-- The restricted deformation keeps every base map induced from the target. -/
theorem deformation_over (hcut : cut < 1) (base : B ⟶ T) :
    (strongDeformationRetract sq cut hcut).H ≫ inclusion sq cut ≫
        TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base =
      fst (Collar sq cut) TopCat.I ≫ inclusion sq cut ≫
        TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base := by
  apply ConcreteCategory.hom_ext
  rintro ⟨z, t⟩
  exact ConcreteCategory.congr_hom
    (TopCat.MappingCylinder.mappingCylinderTargetDeformation_over sq base) (z.val, t)
end TopCat.MappingCylinder.TargetCollar
