/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DeformationRetract.Basic

/-!
# Mapping-cylinder foundations

Interval deformations, canonical projections, and actual homotopy equivalences.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/MappingCylinder/Basic.lean` at
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, homotopies and
pushout universal properties are retained, with native namespace and import ownership.
-/
@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval

universe u

namespace TopCat

/-- Replacing the forward map of a homotopy equivalence by a homotopic
specified map preserves an actual homotopy equivalence. -/
def homotopyEquivOfHomotopy {A B : TopCat.{u}}
    (e : ContinuousMap.HomotopyEquiv A B) {f : A ⟶ B}
    (H : f.hom.Homotopy e.toFun) : ContinuousMap.HomotopyEquiv A B where
  toFun := f.hom
  invFun := e.invFun
  left_inv := ⟨((ContinuousMap.Homotopy.refl e.invFun).comp H).trans e.left_inv.some⟩
  right_inv := ⟨(H.compContinuousMap e.invFun).trans e.right_inv.some⟩


namespace MappingCylinder

/-- Move an interval coordinate linearly toward its terminal endpoint. -/
def intervalSlide (s t : unitInterval) : unitInterval :=
  unitInterval.symm ((unitInterval.symm s) * (unitInterval.symm t))

@[fun_prop]
theorem continuous_intervalSlide :
    Continuous (fun p : unitInterval × unitInterval ↦ intervalSlide p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : unitInterval × unitInterval ↦
    1 - ((1 - (p.1 : ℝ)) * (1 - (p.2 : ℝ))))
  fun_prop

@[simp] theorem intervalSlide_zero (t : unitInterval) : intervalSlide 0 t = t := by
  simp [intervalSlide]
@[simp] theorem intervalSlide_one (t : unitInterval) : intervalSlide 1 t = 1 := by
  simp [intervalSlide]
@[simp] theorem intervalSlide_left (s : unitInterval) : intervalSlide s 0 = s := by
  simp [intervalSlide]
@[simp] theorem intervalSlide_right (s : unitInterval) : intervalSlide s 1 = 1 := by
  simp [intervalSlide]

/-- The terminal endpoint is a strong deformation retract of the cylinder. -/
def cylinderEndpointStrongDeformationRetract (A : TopCat.{u}) :
    CylinderStrongDeformationRetract (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) where
  r := fst A TopCat.I
  retract := TopCat.ι₁_fst A
  H := TopCat.ofHom
    ⟨fun p ↦ (p.1.1, ULift.up (intervalSlide (unitInterval.symm p.2.down) p.1.2.down)),
      continuous_fst.fst.prodMk (continuous_uliftUp.comp
        (continuous_intervalSlide.comp ((unitInterval.continuous_symm.comp
          (continuous_uliftDown.comp continuous_snd)).prodMk
          (continuous_uliftDown.comp continuous_fst.snd))))⟩
  H₀ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    change (a, ULift.up (intervalSlide (unitInterval.symm 0) t.down)) = (a, 1)
    simp only [unitInterval.symm_zero, intervalSlide_one]
    rfl
  H₁ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    change (a, ULift.up (intervalSlide (unitInterval.symm 1) t.down)) = (a, t)
    simp only [unitInterval.symm_one, intervalSlide_zero]
    rfl
  fixed := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    change (a, ULift.up (intervalSlide (unitInterval.symm t.down) 1)) = (a, 1)
    simp only [intervalSlide_right]
    rfl

/-- The usual mapping-cylinder projection, expressed using its actual
pushout universal property. -/
def mappingCylinderProjection {A C M : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) : M ⟶ C :=
  sq.desc (fst A TopCat.I ≫ f) (𝟙 C) (by simp)

@[reassoc (attr := simp)]
theorem mappingCylinderProjection_cylinder {A C M : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) :
    l ≫ mappingCylinderProjection sq = fst A TopCat.I ≫ f := sq.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem mappingCylinderProjection_target {A C M : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) :
    c ≫ mappingCylinderProjection sq = 𝟙 C := sq.inr_desc _ _ _

@[reassoc]
theorem mappingCylinderProjection_start {A C M : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) :
    TopCat.ι₀ ≫ l ≫ mappingCylinderProjection sq = f := by simp

/-- The mapping-cylinder target inclusion is always an actual strong
 deformation retract. -/
def mappingCylinderTargetStrongDeformationRetract {A C M : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) :
    CylinderStrongDeformationRetract c :=
  (cylinderEndpointStrongDeformationRetract A).pushout sq


/-- If the original map is a homotopy equivalence, so is the initial
endpoint inclusion into its mapping cylinder. Its forward map is exactly
the specified initial endpoint inclusion. -/
def mappingCylinderStartHomotopyEquiv {A C M : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
    (e : ContinuousMap.HomotopyEquiv A C) (he : e.toFun = f.hom) :
    ContinuousMap.HomotopyEquiv A M := by
  let ec := (mappingCylinderTargetStrongDeformationRetract sq).toHomotopyEquiv
  let H : TopCat.Homotopy (TopCat.ι₀ ≫ l) (f ≫ c) :=
    homotopyOfCylinder l rfl sq.w
  apply homotopyEquivOfHomotopy (e.trans ec)
  exact H.cast rfl (by change c.hom.comp f.hom = c.hom.comp e.toFun; rw [he])

@[simp]
theorem mappingCylinderStartHomotopyEquiv_toFun {A C M : TopCat.{u}} {f : A ⟶ C}
    {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
    (e : ContinuousMap.HomotopyEquiv A C) (he : e.toFun = f.hom) :
    (mappingCylinderStartHomotopyEquiv sq e he).toFun = (TopCat.ι₀ ≫ l).hom := rfl

end MappingCylinder

end TopCat
