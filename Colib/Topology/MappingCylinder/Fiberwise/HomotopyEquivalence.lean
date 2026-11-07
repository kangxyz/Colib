/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.MappingCylinder.Fiberwise.HomotopyExtension

/-!
# Mapping-cylinder equivalences over the base

The canonical target deformation of a mapping cylinder preserves every
base map induced from its target. A fiberwise inverse for the attaching map
then gives a fiberwise inverse for the source inclusion, with the actual
cylinder paths and both inverse homotopies kept over the same base.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/MappingCylinder/Fiberwise/HomotopyEquivalence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section


noncomputable section

open Topology
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace TopCat.MappingCylinder

/-- The pushed-out deformation restricts to the original deformation on
the cylinder side. -/
@[reassoc]
theorem pushoutDeformation_inl {A B C D : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (h : TopCat.CylinderStrongDeformationRetract i) :
    (g ▷ TopCat.I) ≫ (h.pushout sq).H = h.H ≫ g :=
  (sq.map (tensorRight TopCat.I)).inl_desc _ _ _

/-- On the target side the pushed-out deformation is stationary. -/
@[reassoc]
theorem pushoutDeformation_inr {A B C D : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (h : TopCat.CylinderStrongDeformationRetract i) :
    (j ▷ TopCat.I) ≫ (h.pushout sq).H = fst C TopCat.I ≫ j :=
  (sq.map (tensorRight TopCat.I)).inr_desc _ _ _

variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
  (base : C ⟶ T)

/-- The canonical target deformation does not change the projected base point. -/
theorem mappingCylinderTargetDeformation_over :
    (TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract sq).H ≫
        TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base =
      fst M TopCat.I ≫ TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base := by
  apply (sq.map (tensorRight TopCat.I)).hom_ext
  · change (l ▷ TopCat.I) ≫ _ = _
    rw [← Category.assoc, ← Category.assoc]
    simp only [TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract]
    rw [pushoutDeformation_inl]
    ext ⟨⟨a, s⟩, t⟩
    have hpl := TopCat.MappingCylinder.mappingCylinderProjection_cylinder_assoc sq base
    exact (ConcreteCategory.congr_hom hpl
      (a, ULift.up (TopCat.MappingCylinder.intervalSlide (σ t.down) s.down))).trans
        (ConcreteCategory.congr_hom hpl (a, s)).symm
  · change (c ▷ TopCat.I) ≫ _ = _
    rw [← Category.assoc, ← Category.assoc]
    simp only [TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract]
    rw [pushoutDeformation_inr]
    rfl

/-- The target deformation as an actual continuous homotopy. -/
def mappingCylinderTargetHomotopy :
    TopCat.Homotopy (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ c) (𝟙 M) :=
  TopCat.homotopyOfCylinder
    (TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract sq).H
    (TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract sq).H₀
    (TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract sq).H₁

theorem mappingCylinderTargetHomotopy_over (t : I) (m : M) :
    (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base) (mappingCylinderTargetHomotopy sq
      (t, m)) =
      (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base) m :=
  ConcreteCategory.congr_hom (mappingCylinderTargetDeformation_over sq base) (m, ULift.up t)

/-- The cylinder path from the source inclusion to the target composite. -/
def mappingCylinderSourcePath : TopCat.Homotopy (TopCat.ι₀ ≫ l) (f ≫ c) :=
  TopCat.homotopyOfCylinder l rfl sq.w

theorem mappingCylinderSourcePath_over (t : I) (a : A) :
    (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base) (mappingCylinderSourcePath sq (t,
      a)) = base
      (f a) :=
  ConcreteCategory.congr_hom (TopCat.MappingCylinder.mappingCylinderProjection_cylinder_assoc sq
    base) (a,
    ULift.up t)

/-- A chosen inverse to the attaching map followed by cylinder collapse. -/
def mappingCylinderSourceInverse (g : C ⟶ A) : M ⟶ A :=
  TopCat.MappingCylinder.mappingCylinderProjection sq ≫ g

/-- The attaching map's left inverse homotopy gives the source inclusion's
left inverse homotopy. -/
def mappingCylinderSourceLeftHomotopy (g : C ⟶ A)
    (H : TopCat.Homotopy (f ≫ g) (𝟙 A)) :
    TopCat.Homotopy ((TopCat.ι₀ ≫ l) ≫ mappingCylinderSourceInverse sq g) (𝟙 A) :=
  H.cast (congrArg TopCat.Hom.hom (by
    dsimp [mappingCylinderSourceInverse]
    simp only [Category.assoc, TopCat.MappingCylinder.mappingCylinderProjection_start_assoc])).symm
      rfl

/-- The actual cylinder path, target inverse homotopy, and target
contraction give the source inclusion's right inverse homotopy. -/
def mappingCylinderSourceRightHomotopy (g : C ⟶ A)
    (K : TopCat.Homotopy (g ≫ f) (𝟙 C)) :
    TopCat.Homotopy (mappingCylinderSourceInverse sq g ≫ (TopCat.ι₀ ≫ l)) (𝟙 M) :=
  (((mappingCylinderSourcePath sq).compContinuousMap (mappingCylinderSourceInverse sq g).hom).trans
    (((TopCat.Homotopy.refl c).comp K).compContinuousMap
      (TopCat.MappingCylinder.mappingCylinderProjection
      sq).hom)).trans
      (mappingCylinderTargetHomotopy sq)

/-- A specified inverse for the attaching map gives a genuine source
inclusion equivalence, retaining both explicit inverse homotopies. -/
def mappingCylinderSourceHomotopyEquiv (g : C ⟶ A)
    (H : TopCat.Homotopy (f ≫ g) (𝟙 A)) (K : TopCat.Homotopy (g ≫ f) (𝟙 C)) :
    ContinuousMap.HomotopyEquiv A M where
  toFun := (TopCat.ι₀ ≫ l).hom
  invFun := (mappingCylinderSourceInverse sq g).hom
  left_inv := ⟨mappingCylinderSourceLeftHomotopy sq g H⟩
  right_inv := ⟨mappingCylinderSourceRightHomotopy sq g K⟩

/-- The chosen cylinder inverse is over the fixed base when the original
inverse is over that base. -/
theorem mappingCylinderSourceInverse_over (g : C ⟶ A) (hg : g ≫ f ≫ base = base) :
    mappingCylinderSourceInverse sq g ≫ f ≫ base = TopCat.MappingCylinder.mappingCylinderProjection
      sq ≫ base
      := by
  dsimp [mappingCylinderSourceInverse]
  rw [Category.assoc, hg]

/-- The right inverse homotopy preserves the base point throughout. -/
theorem mappingCylinderSourceRightHomotopy_over (g : C ⟶ A)
    (K : TopCat.Homotopy (g ≫ f) (𝟙 C)) (hg : g ≫ f ≫ base = base)
    (hK : ∀ t x, base (K (t, x)) = base x) (t : I) (m : M) :
    (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base)
      (mappingCylinderSourceRightHomotopy sq g K (t, m)) =
        (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base) m := by
  simp only [mappingCylinderSourceRightHomotopy, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · change (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base)
      (mappingCylinderSourcePath sq (_, mappingCylinderSourceInverse sq g m)) = _
    rw [mappingCylinderSourcePath_over]
    exact ConcreteCategory.congr_hom (mappingCylinderSourceInverse_over sq base g hg) m
  · change (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base)
      (c (K (_, TopCat.MappingCylinder.mappingCylinderProjection sq m))) = _
    exact (ConcreteCategory.congr_hom
      (TopCat.MappingCylinder.mappingCylinderProjection_target_assoc sq base) _).trans (hK _ _)
  · exact mappingCylinderTargetHomotopy_over sq base _ m

end TopCat.MappingCylinder
