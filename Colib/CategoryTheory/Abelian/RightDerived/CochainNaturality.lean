/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.CategoryTheory.Abelian.RightDerived.Cochain

/-!
# Naturality of supplied integer-cochain right-derived comparisons

The existing comparison retains both the actual coefficient map of a supplied resolution
lift and the actual right-derived natural transformation of an additive functor. All
objects and arrows are the native Mathlib and Stacks constructions.

The additive-functor statements are adapted from
`Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, replacing its extension comparison by
`Stacks.DerivedIndexing.mapExtendIso` in the native forward orientation.
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
  {D : Type u'} [Category.{v'} D] [Abelian D]

/-- The inverse comparison retains the actual coefficient map for any supplied lift. -/
@[reassoc]
theorem isoRightDerivedObjCochain_inv_naturality
    (F : C ⥤ D) [F.Additive] {M N : C}
    {I : InjectiveResolution M} {J : InjectiveResolution N} {f : M ⟶ N}
    (φ : Hom I J f) (n : ℕ) :
    homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ) ≫
        (J.isoRightDerivedObjCochain F n).inv =
      (I.isoRightDerivedObjCochain F n).inv ≫ (F.rightDerived n).map f := by
  apply (cancel_mono (J.isoRightDerivedObjCochain F n).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [isoRightDerivedObjCochain_hom_naturality F φ n, Iso.inv_hom_id_assoc]

variable {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)
  {M : C} (I : InjectiveResolution M)

/-- The supplied comparison intertwines the actual right-derived natural transformation. -/
@[reassoc]
theorem isoRightDerivedObjCochain_hom_natTrans (n : ℕ) :
    (NatTrans.rightDerived α n).app M ≫ (I.isoRightDerivedObjCochain G n).hom =
      (I.isoRightDerivedObjCochain F n).hom ≫
        homologyMap ((NatTrans.mapHomologicalComplex α (.up ℤ)).app I.cochainComplex)
          (n : ℤ) := by
  let E₀ := ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  let E₁ := ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  let D₀ := (homologyFunctor D (.up ℤ) (n : ℤ)).mapIso
    (mapExtendIso F ComplexShape.embeddingUpNat I.cocomplex)
  let D₁ := (homologyFunctor D (.up ℤ) (n : ℤ)).mapIso
    (mapExtendIso G ComplexShape.embeddingUpNat I.cocomplex)
  have hδ := congrArg ((homologyFunctor D (.up ℤ) (n : ℤ)).map)
    (mapExtendIso_hom_natTrans α ComplexShape.embeddingUpNat I.cocomplex)
  simp only [Functor.map_comp] at hδ
  change homologyMap
      (extendMap ((NatTrans.mapHomologicalComplex α (.up ℕ)).app I.cocomplex)
        ComplexShape.embeddingUpNat) (n : ℤ) ≫ D₁.hom =
    D₀.hom ≫ homologyMap
      ((NatTrans.mapHomologicalComplex α (.up ℤ)).app I.cochainComplex) (n : ℤ) at hδ
  have hE := HomologicalComplex.extendHomologyIso_hom_naturality
    ((NatTrans.mapHomologicalComplex α (.up ℕ)).app I.cocomplex)
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  change homologyMap
      (extendMap ((NatTrans.mapHomologicalComplex α (.up ℕ)).app I.cocomplex)
        ComplexShape.embeddingUpNat) (n : ℤ) ≫ E₁.hom =
    E₀.hom ≫ homologyMap
      ((NatTrans.mapHomologicalComplex α (.up ℕ)).app I.cocomplex) n at hE
  apply (cancel_mono D₁.inv).mp
  simp only [isoRightDerivedObjCochain_hom, Category.assoc]
  change (NatTrans.rightDerived α n).app M ≫ (I.isoRightDerivedObj G n).hom ≫
      E₁.inv ≫ D₁.hom ≫ D₁.inv =
    (I.isoRightDerivedObj F n).hom ≫ E₀.inv ≫ D₀.hom ≫
      homologyMap ((NatTrans.mapHomologicalComplex α (.up ℤ)).app I.cochainComplex)
        (n : ℤ) ≫ D₁.inv
  rw [← reassoc_of% hδ]
  simp only [Iso.hom_inv_id, Category.comp_id]
  apply (cancel_mono E₁.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hE]
  simp only [Iso.inv_hom_id_assoc]
  rw [InjectiveResolution.rightDerived_app_eq α I n]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The actual derived transformation is computed on the supplied integer resolution. -/
theorem rightDerived_app_eq_cochain (n : ℕ) :
    (NatTrans.rightDerived α n).app M =
      (I.isoRightDerivedObjCochain F n).hom ≫
        homologyMap ((NatTrans.mapHomologicalComplex α (.up ℤ)).app I.cochainComplex)
          (n : ℤ) ≫ (I.isoRightDerivedObjCochain G n).inv := by
  apply (cancel_mono (I.isoRightDerivedObjCochain G n).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact isoRightDerivedObjCochain_hom_natTrans α I n

end CategoryTheory.InjectiveResolution

attribute [colib_ref "aglib_principal_euler_pin"
  "Aglib/Algebra/Homology/DerivedCategory/ExtRightDerived.lean:446-506"
  "adaptation"
  "Actual right-derived natural transformation through the supplied integer-cochain comparison"]
  CategoryTheory.InjectiveResolution.isoRightDerivedObjCochain_hom_natTrans
  CategoryTheory.InjectiveResolution.rightDerived_app_eq_cochain
