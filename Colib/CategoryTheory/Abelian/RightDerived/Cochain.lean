/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.Homology.DerivedIndexing.Extend
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Extend

/-!
# Supplied injective resolutions and integer-indexed right-derived homology

The actual natural-degree right-derived functor is computed on a supplied injective
resolution, extended by zero to integer cochains. The comparison is the composite of
Mathlib's supplied-resolution comparison, its extension homology isomorphism, and the
existing Stacks termwise functor/extension comparison. It retains independent object and
morphism universes for both abelian categories. No derived category is required.

Adapted from `Aglib.CategoryTheory.Abelian.RightDerived.Cochain` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. Its Aglib extension comparison is replaced by
`Stacks.DerivedIndexing.mapExtendIso`, in the opposite orientation. The native extension
functor, resolution, cycles, homology and right-derived functor are all used directly.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Stacks.DerivedIndexing

universe u v u' v'

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]
  {M N : C}

/-- The actual right-derived object is homology of the supplied integer cochain resolution. -/
def isoRightDerivedObjCochain (I : InjectiveResolution M) (n : ℕ) :
    (F.rightDerived n).obj M ≅
      (((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homology (n : ℤ)) :=
  I.isoRightDerivedObj F n ≪≫
    (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).symm ≪≫
    (homologyFunctor D (.up ℤ) (n : ℤ)).mapIso
      (mapExtendIso F ComplexShape.embeddingUpNat I.cocomplex)

/-- The original three comparison factors, with the native Stacks forward orientation. -/
theorem isoRightDerivedObjCochain_hom (I : InjectiveResolution M) (n : ℕ) :
    (isoRightDerivedObjCochain F I n).hom =
      (I.isoRightDerivedObj F n).hom ≫
        (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).inv ≫
        homologyMap (mapExtendIso F ComplexShape.embeddingUpNat I.cocomplex).hom (n : ℤ) :=
  rfl

/-- The comparison retains the actual coefficient map for every supplied resolution lift. -/
@[reassoc]
theorem isoRightDerivedObjCochain_hom_naturality
    {I : InjectiveResolution M} {J : InjectiveResolution N} {f : M ⟶ N}
    (φ : InjectiveResolution.Hom I J f) (n : ℕ) :
    (F.rightDerived n).map f ≫ (isoRightDerivedObjCochain F J n).hom =
      (isoRightDerivedObjCochain F I n).hom ≫
        homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ) := by
  let E₀ := ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  let E₁ := ((F.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  let D₀ := (homologyFunctor D (.up ℤ) (n : ℤ)).mapIso
    (mapExtendIso F ComplexShape.embeddingUpNat I.cocomplex)
  let D₁ := (homologyFunctor D (.up ℤ) (n : ℤ)).mapIso
    (mapExtendIso F ComplexShape.embeddingUpNat J.cocomplex)
  have hδ := congrArg ((homologyFunctor D (.up ℤ) (n : ℤ)).map)
    ((mapExtendNatIso F ComplexShape.embeddingUpNat).hom.naturality φ.hom)
  simp only [Functor.map_comp] at hδ
  change homologyMap
      (extendMap ((F.mapHomologicalComplex (.up ℕ)).map φ.hom)
        ComplexShape.embeddingUpNat) (n : ℤ) ≫ D₁.hom =
    D₀.hom ≫ homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ) at hδ
  have hE := HomologicalComplex.extendHomologyIso_hom_naturality
    ((F.mapHomologicalComplex (.up ℕ)).map φ.hom) ComplexShape.embeddingUpNat
      (j := n) (j' := (n : ℤ)) rfl
  change homologyMap
      (extendMap ((F.mapHomologicalComplex (.up ℕ)).map φ.hom)
        ComplexShape.embeddingUpNat) (n : ℤ) ≫ E₁.hom =
    E₀.hom ≫ homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ.hom) n at hE
  have hc : I.ι.f 0 ≫ φ.hom.f 0 = f ≫ J.ι.f 0 := by
    simpa only [CochainComplex.single₀_map_f_zero] using φ.ι_f_zero_comp_hom_f_zero
  apply (cancel_mono D₁.inv).mp
  simp only [isoRightDerivedObjCochain_hom, Category.assoc]
  change (F.rightDerived n).map f ≫ (J.isoRightDerivedObj F n).hom ≫
      E₁.inv ≫ D₁.hom ≫ D₁.inv =
    (I.isoRightDerivedObj F n).hom ≫ E₀.inv ≫ D₀.hom ≫
      homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ) ≫ D₁.inv
  rw [← reassoc_of% hδ]
  simp only [Iso.hom_inv_id, Category.comp_id]
  apply (cancel_mono E₁.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hE]
  simp only [Iso.inv_hom_id_assoc]
  exact InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ.hom hc F n

omit [EnoughInjectives C] in
/-- The actual zero cycles of the mapped supplied integer resolution. -/
def toRightDerivedZeroCochainCycles (I : InjectiveResolution M) : F.obj M ⟶
    (((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).cycles 0) :=
  I.toRightDerivedZero' F ≫
    (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendCyclesIso
      ComplexShape.embeddingUpNat (j := 0) (j' := 0) rfl).inv ≫
    cyclesMap (mapExtendIso F ComplexShape.embeddingUpNat I.cocomplex).hom 0

omit [EnoughInjectives C] in
/-- The zero-cycle map retains the actual resolution augmentation in degree zero. -/
@[reassoc]
theorem toRightDerivedZeroCochainCycles_comp_iCycles (I : InjectiveResolution M) :
    toRightDerivedZeroCochainCycles F I ≫
        ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).iCycles 0 =
      F.map (I.ι.f 0) ≫ F.map (I.cochainComplexXIso 0 0 rfl).inv := by
  dsimp only [toRightDerivedZeroCochainCycles]
  simp only [Category.assoc]
  erw [cyclesMap_i, extendCyclesIso_inv_iCycles_assoc,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
  rw [extendXIso_inv_comp_mapExtendIso_hom_f]
  rfl

/-- The actual transformation to the zeroth right-derived functor is the zero-cycle projection. -/
@[reassoc]
theorem toRightDerivedZero_comp_isoRightDerivedObjCochain (I : InjectiveResolution M) :
    F.toRightDerivedZero.app M ≫ (I.isoRightDerivedObjCochain F 0).hom =
      toRightDerivedZeroCochainCycles F I ≫
        ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homologyπ 0 := by
  rw [I.toRightDerivedZero_eq F, isoRightDerivedObjCochain_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change I.toRightDerivedZero' F ≫
      ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ 0 ≫
        (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat (j := 0) (j' := 0) rfl).inv ≫
        homologyMap (mapExtendIso F ComplexShape.embeddingUpNat I.cocomplex).hom 0 = _
  rw [homologyπ_extendHomologyIso_inv_assoc, homologyπ_naturality]
  simp only [toRightDerivedZeroCochainCycles, Category.assoc]
  rfl

end CategoryTheory.InjectiveResolution
