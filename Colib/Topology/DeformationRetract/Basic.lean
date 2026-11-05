/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.Cylinder
public import Mathlib.Topology.Homotopy.TopCat.Basic
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Cylinder strong deformation retractions

Explicit deformation retract data and its preservation under topological pushouts.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/DeformationRetract/Basic.lean` at
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, homotopies and
pushout universal properties are retained, with native namespace and import ownership.
-/
@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval

universe u

namespace TopCat

/-- Cylinder coordinates give an ordinary continuous homotopy. -/
def homotopyOfCylinder {A B : TopCat.{u}} {f g : A ⟶ B}
    (H : A ⊗ TopCat.I ⟶ B) (h₀ : TopCat.ι₀ ≫ H = f) (h₁ : TopCat.ι₁ ≫ H = g) :
    f.hom.Homotopy g.hom where
  toFun p := H (p.2, ULift.up p.1)
  continuous_toFun := H.hom.continuous.comp
    (continuous_snd.prodMk (continuous_uliftUp.comp continuous_fst))
  map_zero_left a := ConcreteCategory.congr_hom h₀ a
  map_one_left a := ConcreteCategory.congr_hom h₁ a

/-- Explicit strong deformation retraction data for a specified inclusion. -/
structure CylinderStrongDeformationRetract {A B : TopCat.{u}} (i : A ⟶ B) where
  /-- The actual continuous retraction. -/
  r : B ⟶ A
  /-- The retraction is exact on the subspace. -/
  retract : i ≫ r = 𝟙 A
  /-- The deformation from retraction followed by inclusion to the identity. -/
  H : B ⊗ TopCat.I ⟶ B
  H₀ : TopCat.ι₀ ≫ H = r ≫ i
  H₁ : TopCat.ι₁ ≫ H = 𝟙 B
  /-- The entire deformation fixes the included subspace. -/
  fixed : (i ▷ TopCat.I) ≫ H = fst A TopCat.I ≫ i

/-- Strong deformation retraction data is a genuine topological homotopy equivalence. -/
def CylinderStrongDeformationRetract.toHomotopyEquiv {A B : TopCat.{u}} {i : A ⟶ B}
    (h : CylinderStrongDeformationRetract i) : ContinuousMap.HomotopyEquiv A B where
  toFun := i.hom
  invFun := h.r.hom
  left_inv := by
    have heq : h.r.hom.comp i.hom = ContinuousMap.id A :=
      congrArg TopCat.Hom.hom h.retract
    rw [heq]
  right_inv := ⟨homotopyOfCylinder h.H h.H₀ h.H₁⟩

@[simp]
theorem CylinderStrongDeformationRetract.toHomotopyEquiv_toFun
    {A B : TopCat.{u}} {i : A ⟶ B} (h : CylinderStrongDeformationRetract i) :
    h.toHomotopyEquiv.toFun = i.hom := rfl

/-- Strong deformation retractions are preserved under arbitrary topological pushouts. -/
def CylinderStrongDeformationRetract.pushout {A B C D : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (h : CylinderStrongDeformationRetract i) :
    CylinderStrongDeformationRetract j := by
  have hw : i ≫ h.r ≫ f = f ≫ 𝟙 C := by
    rw [← Category.assoc, h.retract]
    simp
  let r := sq.desc (h.r ≫ f) (𝟙 C) hw
  have hgr : g ≫ r = h.r ≫ f := sq.inl_desc _ _ _
  have hjr : j ≫ r = 𝟙 C := sq.inr_desc _ _ _
  have sqI : IsPushout (i ▷ TopCat.I) (f ▷ TopCat.I)
      (g ▷ TopCat.I) (j ▷ TopCat.I) := sq.map (tensorRight TopCat.I)
  have hwH : (i ▷ TopCat.I) ≫ h.H ≫ g =
      (f ▷ TopCat.I) ≫ fst C TopCat.I ≫ j := by
    rw [← Category.assoc, h.fixed, Category.assoc, sq.w,
      ← Category.assoc, ← whiskerRight_fst, Category.assoc]
  let H := sqI.desc (h.H ≫ g) (fst C TopCat.I ≫ j) hwH
  have hgH : (g ▷ TopCat.I) ≫ H = h.H ≫ g := sqI.inl_desc _ _ _
  have hjH : (j ▷ TopCat.I) ≫ H = fst C TopCat.I ≫ j := sqI.inr_desc _ _ _
  refine ⟨r, hjr, H, ?_, ?_, hjH⟩
  · apply sq.hom_ext
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hgH,
        ← Category.assoc, h.H₀]
      rw [← Category.assoc, hgr, Category.assoc, sq.w, ← Category.assoc]
    · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hjH,
        ← Category.assoc, TopCat.ι₀_fst, Category.id_comp,
        ← Category.assoc, hjr, Category.id_comp]
  · apply sq.hom_ext
    · rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hgH,
        ← Category.assoc, h.H₁]
      simp
    · rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc, hjH,
        ← Category.assoc, TopCat.ι₁_fst]
      simp

/-- The canonical map obtained by pushing out a strong deformation retract
is the forward map of a genuine homotopy equivalence. -/
def pushoutStrongDeformationRetractHomotopyEquiv {A B C D : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (h : CylinderStrongDeformationRetract i) :
    ContinuousMap.HomotopyEquiv C D :=
  (h.pushout sq).toHomotopyEquiv

@[simp]
theorem pushoutStrongDeformationRetractHomotopyEquiv_toFun {A B C D : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (h : CylinderStrongDeformationRetract i) :
    (pushoutStrongDeformationRetractHomotopyEquiv sq h).toFun = j.hom := rfl

end TopCat
